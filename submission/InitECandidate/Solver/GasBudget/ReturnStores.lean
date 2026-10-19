import InitECandidate.Solver.GasBudget.ReturnProgram

namespace InitECandidate.Solver.GasBudget.ReturnOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def writes (frame base start size : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(frame + 120#64, base + start), (frame + 128#64, size), (frame + 104#64, 0#64)]

theorem stores_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch start size : BitVec 64)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "s") = some (.val (.word start)))
    (sizeLocal : source.locals.lookup (ofString "n") = some (.val (.word size)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source stores = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ post = emptyLocalsHOLFinite {source with memory := WordWrites.write source.memory (writes frame base start size)} := by
  have firstSafe : Input.LocalPrefix (ofString "n") (.store (frameAddress 120#64) outputAddress) := .store _ _
  obtain ⟨first, firstRun, restRun, retained⟩ := firstSafe.normal_continue source post _ returned normal
  have baseRead := frame_read source frame 24#64 base view.ev (view.mapped 24 (by simp)) view.baseCell
  have addressRead : eval source outputAddress = some (.val (.word (base + start))) := by
    simp only [eval] at baseRead
    simp [eval, outputAddress, evalHOLExact, evalListHOLExact, toExact, localVar, startLocal, baseRead, valueIsWord, valueWord, wordOpHOL, wordOp]
  have firstEq := FrameField.normal_word source first frame 120#64 (base + start) outputAddress view.ev addressRead firstRun
  have secondSafe : Input.LocalPrefix (ofString "n") (.store (frameAddress 128#64) (localVar "n")) := .store _ _
  obtain ⟨second, secondRun, finalRun, saved⟩ := secondSafe.normal_continue first post _ returned restRun
  have firstEv : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstEq]; exact view.ev
  have sizeRead : eval first (localVar "n") = some (.val (.word size)) := by
    have cell := retained.trans sizeLocal
    simp [eval, evalHOLExact, toExact, localVar, cell]
  have secondEq := FrameField.normal_word first second frame 128#64 size (localVar "n") firstEv sizeRead secondRun
  have thirdSafe : Input.LocalPrefix (ofString "n") (.store (frameAddress 104#64) (.const 0#64)) := .store _ _
  obtain ⟨third, thirdRun, returnRun, kept⟩ := thirdSafe.normal_continue second post _ returned finalRun
  have secondEv : second.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [secondEq, firstEq]; exact view.ev
  have thirdEq := FrameField.normal_word second third frame 104#64 0#64 (.const 0#64) secondEv rfl thirdRun
  obtain ⟨read, postEq⟩ := Input.return_normal third post (.const 0#64) returned returnRun
  have value : returned = .val (.word 0#64) := by simpa [eval, evalHOLExact] using (Option.some.inj read).symm
  refine ⟨value, ?_⟩
  rw [postEq, thirdEq, secondEq, firstEq]
  rfl

theorem writes_away (memory : WordWrites.Memory) (frame base start size query : BitVec 64)
    (notOutput : query ≠ frame + 120#64) (notSize : query ≠ frame + 128#64) (notRunning : query ≠ frame + 104#64) :
    WordWrites.write memory (writes frame base start size) query = memory query := by
  apply WordWrites.write_away
  simp [writes, notOutput, notSize, notRunning]

theorem writes_running (memory : WordWrites.Memory) (frame base start size : BitVec 64) :
    WordWrites.write memory (writes frame base start size) (frame + 104#64) = .word 0#64 := by
  simp [writes, WordWrites.write, StoreWord.put]

end InitECandidate.Solver.GasBudget.ReturnOpcode

#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.stores_normal
#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.writes_away
#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.writes_running

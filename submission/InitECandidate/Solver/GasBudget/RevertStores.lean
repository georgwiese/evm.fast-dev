import InitECandidate.Solver.GasBudget.RevertProgram
import InitECandidate.Solver.Input.ExceptionAfterPrefix

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def writes (frame base start size : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(frame + 120#64, base + start), (frame + 128#64, size)]

theorem stores_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch start size : BitVec 64)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "s") = some (.val (.word start)))
    (sizeLocal : source.locals.lookup (ofString "n") = some (.val (.word size)))
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source stores = (some (.exception identifier payload), post)) :
    identifier = ofString "EvmErr" ∧ payload = .val (.word 1#64) ∧
      post = emptyLocalsHOLFinite {source with memory := WordWrites.write source.memory (writes frame base start size)} := by
  have firstSafe := Input.NoException.store source.code (frameAddress 120#64) outputAddress source rfl identifier payload
  obtain ⟨first, firstRun, restRun⟩ := Input.sequence_exception_after source post _ _ identifier payload firstSafe run
  have baseRead := frame_read source frame 24#64 base view.ev (view.mapped 24 (by simp)) view.baseCell
  have addressRead : eval source outputAddress = some (.val (.word (base + start))) := by
    simp only [eval] at baseRead
    simp [eval, outputAddress, evalHOLExact, evalListHOLExact, toExact, localVar, startLocal, baseRead, valueIsWord, valueWord, wordOpHOL, wordOp]
  have firstEq := FrameField.normal_word source first frame 120#64 (base + start) outputAddress view.ev addressRead firstRun
  have secondSafe := Input.NoException.store first.code (frameAddress 128#64) (localVar "n") first rfl identifier payload
  obtain ⟨second, secondRun, finalRun⟩ := Input.sequence_exception_after first post _ _ identifier payload secondSafe restRun
  have firstEv : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstEq]; exact view.ev
  have sizeRead : eval first (localVar "n") = some (.val (.word size)) := by
    have cell : first.locals.lookup (ofString "n") = some (.val (.word size)) := by rw [firstEq]; exact sizeLocal
    simp [eval, evalHOLExact, toExact, localVar, cell]
  have secondEq := FrameField.normal_word first second frame 128#64 size (localVar "n") firstEv sizeRead secondRun
  have secondShape : second.eshapes.lookup (ofString "EvmErr") = some .one := by rw [secondEq, firstEq]; exact shape
  have raised : evaluateHOLFiniteState second (.raise (ofString "EvmErr") (.const 1#64)) =
      (some (.exception (ofString "EvmErr") (.val (.word 1#64))), emptyLocalsHOLFinite second) := by
    simp [evaluateHOLFiniteState_raise, evalHOLExact, secondShape, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [StateSteps.stopped_sequence second _ _ MemoryExtend.returnZero _ raised (Nat.le_refl _)] at finalRun
  have ids : identifier = ofString "EvmErr" ∧ payload = .val (.word 1#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.exception.injEq] using (congrArg Prod.fst finalRun).symm
  have postEq : post = emptyLocalsHOLFinite second := (congrArg Prod.snd finalRun).symm
  refine ⟨ids.1, ids.2, ?_⟩
  rw [postEq, secondEq, firstEq]
  rfl

theorem writes_away (memory : WordWrites.Memory) (frame base start size query : BitVec 64)
    (notOutput : query ≠ frame + 120#64) (notSize : query ≠ frame + 128#64) :
    WordWrites.write memory (writes frame base start size) query = memory query := by
  apply WordWrites.write_away
  simp [writes, notOutput, notSize]

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.stores_exception
#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.writes_away

import InitECandidate.Solver.Input.CurrentTable.FirstDiff.BitLoopNormal

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- A real fallthrough of the actual declared bit scan forces its byte to
zero, rather than assuming a successful later bit scan. -/
theorem different_none_zero (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8)
    (wordCell : source.locals.lookup (ofString "x") = some (.val (.word (byte.setWidth 64))))
    (normal : evaluateHOLFiniteState source different = (none,post)) : byte = 0#8 := by
  rw [shapes.2.2.2.2.2.2.1] at normal
  obtain ⟨inner,run,endpoint⟩ := declaration_none source post "j" (.const 0#64) 0#64 bitLoop
    (by simp [eval,evalHOLExact]) normal
  have ready : BitInvariant byte (bind source "j" 0#64) := by
    refine ⟨0,by decide,bind_lookup_same _ _ _,?_,?_⟩
    · exact (bind_lookup_other source "j" "x" 0#64 (by decide)).trans wordCell
    · intro prior before
      omega
  exact bit_loop_none_zero _ inner byte ready run

theorem choice_none_zero (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8)
    (wordCell : source.locals.lookup (ofString "x") = some (.val (.word (byte.setWidth 64))))
    (normal : evaluateHOLFiniteState source choice = (none,post)) : byte = 0#8 := by
  by_cases zero : byte.setWidth 64 = 0#64
  · have narrow := congrArg (BitVec.setWidth 8) zero
    simpa using narrow
  · rw [shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite] at normal
    have read : eval source (.cmp .notEqual (localVar "x") (.const 0#64)) = some (.val (.word 1#64)) := by
      simp [eval,evalHOLExact,localVar,wordCell,wordCmpHOL,zero]
    simp only [eval] at read
    rw [read] at normal
    simp only [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)] at normal
    exact different_none_zero source post byte wordCell normal

/-- A continuing outer step read equal bytes. All other byte values force
an actual return or stopped outcome inside the current bit scan. -/
theorem step_none_zero (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (byte : BitVec 8)
    (read : eval source readX = some (.val (.word (byte.setWidth 64))))
    (normal : evaluateHOLFiniteState source step = (none,post)) : byte = 0#8 := by
  rw [shapes.2.2.2.1] at normal
  obtain ⟨inner,run,endpoint⟩ := declaration_none source post "x" readX (byte.setWidth 64) afterX read normal
  rw [shapes.2.2.2.2.1] at run
  obtain ⟨middle,choiceRun,incrementRun⟩ := sequence_none _ inner _ _ run
  exact choice_none_zero _ middle byte (bind_lookup_same source "x" _) choiceRun

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.different_none_zero
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.choice_none_zero
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.step_none_zero

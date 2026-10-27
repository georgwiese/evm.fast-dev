import InitECandidate.Solver.Input.NonTimeoutSequenceCall

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A scoped helper in an actual non-timeout enclosing run has a funded
caller and a genuine non-timeout callee execution. No return or successful
continuation is assumed. -/
theorem scoped_call_non_timeout {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,returnShape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall name shape function arguments continuation) = (result,target))
    (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1 ≠ some .timeOut := by
  have funded : 1 ≤ source.clock := by
    by_cases zero : source.clock = 0
    · have actual := run
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at actual
      simp only [args, called, if_pos zero] at actual
      have bad := congrArg Prod.fst actual
      exact (notTimeout bad.symm).elim
    · omega
  refine ⟨funded,?_⟩
  intro timed
  have bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body =
      (some .timeOut,(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2) := Prod.ext timed rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
  simp only [args,called,if_neg (show source.clock ≠ 0 by omega)] at run
  rw [bodyRun] at run
  have bad := congrArg Prod.fst run
  exact notTimeout bad.symm

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.scoped_call_non_timeout

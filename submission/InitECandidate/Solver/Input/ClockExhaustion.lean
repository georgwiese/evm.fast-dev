import InitECandidate.Solver.Input.TerminatingPaddedScope

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- If a real padded execution has less clock left than the padding, the
original execution must time out. This uses the actual semantic clock-shift
theorem and does not assume a successful unpadded execution. -/
theorem timeout_of_padded_remainder {F : Type} (source post : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    (padding : Nat) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState {source with clock := source.clock + padding} program = (result,post)) (short : post.clock < padding) :
    (evaluateHOLFiniteState source program).1 = some .timeOut := by
  by_contra notTimeout
  have actual := panPropsEvaluateAddClockEq program source (evaluateHOLFiniteState source program).1 (evaluateHOLFiniteState source program).2 padding ⟨rfl,notTimeout⟩
  have same := congrArg (fun output => output.2.clock) (run.symm.trans actual)
  change post.clock = (evaluateHOLFiniteState source program).2.clock + padding at same
  omega

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.timeout_of_padded_remainder

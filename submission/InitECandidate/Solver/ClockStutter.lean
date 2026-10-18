import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A non-timeout execution cannot produce the identical result/state when
started from the same state with strictly less clock. This excludes a
no-change loop iteration on a covered terminating execution, without
requiring unconditional termination or a logical data-structure invariant. -/
theorem no_clock_stutter {F : Type} (source target : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (smaller : Nat) (strict : smaller < source.clock)
    (normal : evaluateHOLFiniteState source program = (result, target)) (notTimeout : result ≠ some .timeOut)
    (stutter : evaluateHOLFiniteState {source with clock := smaller} program = (result, target)) : False := by
  let low := {source with clock := smaller}
  have shifted := panPropsEvaluateAddClockEq program low result target (source.clock - smaller) ⟨stutter, notTimeout⟩
  have restored : {low with clock := low.clock + (source.clock - smaller)} = source := by
    change {source with clock := smaller + (source.clock - smaller)} = source
    have add : smaller + (source.clock - smaller) = source.clock := by omega
    rw [add]
  rw [restored, normal] at shifted
  have sameClock := congrArg (fun output : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F => output.2.clock) shifted
  change target.clock = target.clock + (source.clock - smaller) at sameClock
  omega

end InitECandidate.Solver

#print axioms InitECandidate.Solver.no_clock_stutter

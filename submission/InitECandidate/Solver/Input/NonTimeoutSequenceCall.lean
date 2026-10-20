import InitECandidate.Solver.Input.TerminatingPaddedSequence
import InitECandidate.Solver.Input.ClockExhaustion

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A timeout in an actual sequence prefix cannot enter its continuation. -/
theorem sequence_timeout {F : Type} (source : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (timed : (evaluateHOLFiniteState source first).1 = some .timeOut) :
    (evaluateHOLFiniteState source (.seq first second)).1 = some .timeOut := by
  have actual : evaluateHOLFiniteState source first = (some .timeOut,(evaluateHOLFiniteState source first).2) := Prod.ext timed rfl
  rw [evaluateHOLFiniteState_seq_line780,actual]

/-- Any actual non-timeout sequence beginning with a known ordinary/caught
call derives its caller tick and a non-timeout execution of the real callee.
Catching an exception cannot catch a timeout. -/
theorem sequence_call_non_timeout {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,shape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call info function arguments) continuation) = (result,target))
    (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1 ≠ some .timeOut := by
  have stop (timed : (evaluateHOLFiniteState source (.call info function arguments)).1 = some .timeOut) : False := by
    have whole := sequence_timeout source (.call info function arguments) continuation timed
    rw [run] at whole
    exact notTimeout whole
  have funded : 1 ≤ source.clock := by
    by_contra insufficient
    have zero : source.clock = 0 := by omega
    apply stop
    rw [evaluateHOLFiniteState_call,args]
    simp only [called,if_pos zero]
  refine ⟨funded,?_⟩
  intro timed
  apply stop
  have actual : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body =
      (some .timeOut,(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2) := Prod.ext timed rfl
  rw [evaluateHOLFiniteState_call,args]
  simp only [called,if_neg (show source.clock ≠ 0 by omega)]
  rw [actual]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_timeout
#print axioms InitECandidate.Solver.Input.sequence_call_non_timeout

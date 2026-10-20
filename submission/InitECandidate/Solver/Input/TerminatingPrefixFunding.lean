import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A fixed reached phase derives its actual funding from termination of
the enclosing execution. Its executor is proved at all sufficient clocks;
clock padding handles insufficient-clock cases without assuming success. -/
theorem terminating_prefix {F : Type} (source post template : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (price : Nat) (result : Option (PanSemResultExact 64))
    (execute : ∀ clock,price ≤ clock → evaluateHOLFiniteState {source with clock := clock} first =
      (none,{template with clock := clock - price}))
    (normal : evaluateHOLFiniteState source (.seq first second) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    price ≤ source.clock ∧ evaluateHOLFiniteState {template with clock := source.clock - price} second = (result,post) := by
  have padded := panPropsEvaluateAddClockEq (.seq first second) source result post price ⟨normal,notTimeout⟩
  have firstRun := execute (source.clock + price) (by omega)
  simp only [Nat.add_sub_cancel_right] at firstRun
  rw [evaluateHOLFiniteState_seq_line780] at padded
  simp only [firstRun] at padded
  have remaining := evaluateHOLFiniteState_clock_le {template with clock := source.clock} second
  rw [padded] at remaining
  change post.clock + price ≤ source.clock at remaining
  have funded : price ≤ source.clock := by omega
  have actual := execute source.clock funded
  change evaluateHOLFiniteState source first = (none,{template with clock := source.clock - price}) at actual
  rw [evaluateHOLFiniteState_seq_line780] at normal
  simp only [actual] at normal
  exact ⟨funded,normal⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.terminating_prefix

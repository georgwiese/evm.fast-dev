import InitECandidate.Solver.Input.ControlContinue

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A taken iteration of an actually ordinary while outcome exposes an ordinary body
control result. It does not assume that break/continue are unreachable; the
specific reachable body must discharge those alternatives afterwards. -/
theorem while_control_body {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64)
    (read : eval source condition = some (.val (.word 1#64)))
    (result : Option (PanSemResultExact 64)) (control : ControlResult result)
    (normal : evaluateHOLFiniteState source (.while condition body) = (result, target)) :
    1 ≤ source.clock ∧ ∃ middle result,
      evaluateHOLFiniteState (decClockHOLFinite source) body = (result, middle) ∧
      ControlResult result ∧ middle.clock ≤ source.clock - 1 := by
  classical
  rw [evaluateHOLFiniteState_while_total] at normal
  simp only [eval, evalHOLFinite] at read normal
  rw [read] at normal
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide)] at normal
  by_cases zero : source.clock = 0
  · rw [if_pos zero] at normal
    cases control <;> cases normal
  · rw [if_neg zero] at normal
    let entry := decClockHOLFinite source
    have clock := evaluateHOLFiniteState_clock_le entry body
    generalize computed : evaluateHOLFiniteState entry body = output at normal clock
    obtain ⟨result, middle⟩ := output
    rw [WitnessRadix.StateSteps.fixed_clock entry middle result clock] at normal
    have bounded : middle.clock ≤ source.clock - 1 := clock
    refine ⟨by omega, middle, result, rfl, ?_, bounded⟩
    cases result with
    | none => exact .next
    | some result =>
      cases result with
      | «break» => exact .breaks
      | «continue» => exact .continues
      | returned value => exact .returned value
      | error => cases control <;> cases normal
      | timeOut => cases control <;> cases normal
      | exception identifier payload => cases control <;> cases normal
      | finalFfi event => cases control <;> cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.while_control_body

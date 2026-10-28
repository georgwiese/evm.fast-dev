import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.GlobalByteEffects

namespace InitECandidate.Solver.Input.StraightBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Checked source syntax with no calls, loops, clock ticks or global writes.
The expressions and memory operations still have real straight-line target work. -/
def accepts : ProgHOL 64 → Bool
  | .skip | .assign .local _ _ | .store _ _ | .storeByte _ _ | .return _ | .raise _ _ | .break | .continue => true
  | .seq first second => accepts first && accepts second
  | .ite _ yes no => accepts yes && accepts no
  | .dec _ _ _ body => accepts body
  | _ => false

theorem byte_clock (code) (address value : ExpHOL 64) : QuietClock.Preserves code (.storeByte address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

/-- Structural soundness applies to every actual outcome, including expression
and memory errors. It assumes no successful input reads or returned result. -/
theorem effects (selected : MlS) (code) (program : ProgHOL 64) (checked : accepts program = true) :
    QuietClock.Preserves code program ∧ GlobalEffects.Preserves selected code program := by
  cases program with
  | skip => exact ⟨QuietClock.skip code, GlobalEffects.skip selected code⟩
  | assign kind name expression =>
    cases kind with
    | «local» => exact ⟨QuietClock.assign code name expression, GlobalEffects.assign selected code name expression⟩
    | «global» => cases checked
  | store address value => exact ⟨QuietClock.store code address value, GlobalEffects.store selected code address value⟩
  | storeByte address value => exact ⟨byte_clock code address value, GlobalEffects.byte_store selected code address value⟩
  | «return» expression => exact ⟨QuietClock.returned code expression, GlobalEffects.returned selected code expression⟩
  | «raise» name expression => exact ⟨QuietClock.raised code name expression, GlobalEffects.raised selected code name expression⟩
  | «break» => exact ⟨(QuietClock.stopped code).1, (GlobalEffects.stopped selected code).1⟩
  | «continue» => exact ⟨(QuietClock.stopped code).2, (GlobalEffects.stopped selected code).2⟩
  | seq first second =>
    have parts : accepts first = true ∧ accepts second = true := by simpa only [accepts, Bool.and_eq_true] using checked
    obtain ⟨left, right⟩ := parts
    exact ⟨QuietClock.sequence code first second (effects selected code first left).1 (effects selected code second right).1,
      GlobalEffects.sequence selected code first second (effects selected code first left).2 (effects selected code second right).2⟩
  | ite test yes no =>
    have parts : accepts yes = true ∧ accepts no = true := by simpa only [accepts, Bool.and_eq_true] using checked
    obtain ⟨left, right⟩ := parts
    exact ⟨QuietClock.conditional code test yes no (effects selected code yes left).1 (effects selected code no right).1,
      GlobalEffects.conditional selected code test yes no (effects selected code yes left).2 (effects selected code no right).2⟩
  | dec name shape expression body =>
    exact ⟨QuietClock.declared code name shape expression body (effects selected code body checked).1,
      GlobalEffects.declared selected code name shape expression body (effects selected code body checked).2⟩
  | _ => simp only [accepts] at checked; cases checked
termination_by structural program

end InitECandidate.Solver.Input.StraightBody

#print axioms InitECandidate.Solver.Input.StraightBody.byte_clock
#print axioms InitECandidate.Solver.Input.StraightBody.effects

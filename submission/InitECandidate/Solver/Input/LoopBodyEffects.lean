import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.GlobalEffectsLoop

namespace InitECandidate.Solver.Input.LoopBodyEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Call-free source syntax whose assignments are local. Loops can consume
clock and memory writes can fail; neither can change a global binding. -/
def accepts : ProgHOL 64 → Bool
  | .seq first second => accepts first && accepts second
  | .ite _ yes no => accepts yes && accepts no
  | .dec _ _ _ body => accepts body
  | .while _ body => accepts body
  | atom => StraightBody.accepts atom

theorem sound (key : MlS) (code) (program : ProgHOL 64) (checked : accepts program = true) :
    GlobalEffects.Preserves key code program := by
  cases program with
  | seq first second =>
    have parts : accepts first = true ∧ accepts second = true := by simpa only [accepts,Bool.and_eq_true] using checked
    exact GlobalEffects.sequence key code first second (sound key code first parts.1) (sound key code second parts.2)
  | ite test yes no =>
    have parts : accepts yes = true ∧ accepts no = true := by simpa only [accepts,Bool.and_eq_true] using checked
    exact GlobalEffects.conditional key code test yes no (sound key code yes parts.1) (sound key code no parts.2)
  | dec name shape expression body =>
    exact GlobalEffects.declared key code name shape expression body (sound key code body checked)
  | «while» test body =>
    exact GlobalEffects.loop key code test body (sound key code body checked)
  | _ => exact (StraightBody.effects key code _ checked).2
termination_by structural program

end InitECandidate.Solver.Input.LoopBodyEffects

#print axioms InitECandidate.Solver.Input.LoopBodyEffects.sound

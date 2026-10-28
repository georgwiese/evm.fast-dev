import InitECandidate.Solver.Input.CurrentTable.Get.Program
import InitECandidate.Solver.Input.MemeqCode
import InitECandidate.Solver.Input.MemeqReadOnly
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Every actual current lookup outcome preserves the complete physical
state. Invalid arguments/reads and short clocks are included. -/
theorem body_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code body := by
  rw [body_shape]
  apply LocalEffects.scoped_body code _ _ _ _ _ FindLeaf.formals FindLeaf.body .one
    (FindLeaf.original_code code installed) (FindLeaf.body_readonly code)
  unfold afterLeaf emptyGuard absent afterEmpty afterLength afterStride compareCall afterCompare compareGuard
  apply LocalEffects.sequence
  · exact LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)
  · apply LocalEffects.declared
    apply LocalEffects.declared
    apply LocalEffects.declared
    apply LocalEffects.scoped_body code _ _ _ _ _ Memeq32.formals Memeq32.body .one
      (MutableTable.MemeqAny.original_code code installed) (MutableTable.MemeqAny.readonly code)
    exact LocalEffects.sequence code _ _
      (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)) (LocalEffects.returned code _)

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.body_readonly

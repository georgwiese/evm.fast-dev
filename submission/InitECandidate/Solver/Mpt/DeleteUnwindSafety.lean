import InitECandidate.Solver.Mpt.DeleteUnwindProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Assigned helpers restore caller control. The original unwind body
cannot silently break, continue or return from its caller. -/
theorem unwind_body_safe : Input.LocalPrefix (ofString "key") unwindBody := by
  rw [unwind_shapes.2.1,unwind_shapes.2.2.1,choice_shape,unwind_shapes.2.2.2.2]
  unfold finishExtension branchUnwind replaceChild finishBranch
  repeat first
    | apply Input.LocalPrefix.dec <;> (try decide)
    | apply Input.LocalPrefix.seq
    | apply Input.LocalPrefix.ite
    | exact Input.LocalPrefix.assign _ _ (by decide)
    | exact Input.LocalPrefix.store _ _
    | exact Input.LocalPrefix.call (some (ofString "res")) _ _ (by intro name same; have equal:=Option.some.inj same; subst name; decide)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_body_safe

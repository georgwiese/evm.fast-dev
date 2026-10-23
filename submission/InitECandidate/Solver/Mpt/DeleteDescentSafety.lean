import InitECandidate.Solver.Mpt.DeleteDescentBranchProgram
import InitECandidate.Solver.Mpt.DeleteFrameProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Every original descent continuation restores caller control. Neither
a helper return nor a scoped allocator can act as a caller break/return. -/
theorem descent_body_safe : Input.LocalPrefix (ofString "key") descentBody := by
  have pushSafe (kind : DeleteFrame.Kind) : Input.LocalPrefix (ofString "key") kind.push:=by
    rw [kind.push_shape (fun _=>0#64)]
    cases kind <;> simp only [DeleteFrame.Kind.fields,DeleteFrame.Kind.name,DeleteFrame.Kind.advance,LocalFields.program]
    all_goals repeat first
      | apply Input.LocalPrefix.seq
      | exact Input.LocalPrefix.store _ _
      | exact Input.LocalPrefix.assign _ _ (by decide)
  simp only [descent_shapes.2.1,descent_shapes.2.2.1,descent_shapes.2.2.2.1,descent_shapes.2.2.2.2.1,
    descent_shapes.2.2.2.2.2.1,descent_shapes.2.2.2.2.2.2.1,descent_shapes.2.2.2.2.2.2.2.1,descent_shapes.2.2.2.2.2.2.2.2,
    leaf_shape,extension_shapes.1,extension_shapes.2.1,extension_shapes.2.2.1,extension_shapes.2.2.2.1,extension_shapes.2.2.2.2,
    branch_shapes.1,branch_shapes.2.1,branch_shapes.2.2.1,branch_shapes.2.2.2]
  repeat first
    | exact pushSafe .extension
    | exact pushSafe .branch
    | apply Input.LocalPrefix.dec <;> (try decide)
    | apply Input.LocalPrefix.decCall <;> (try decide)
    | apply Input.LocalPrefix.seq
    | apply Input.LocalPrefix.ite
    | exact Input.LocalPrefix.assign _ _ (by decide)
    | exact Input.LocalPrefix.store _ _
    | exact Input.LocalPrefix.skip
    | exact Input.LocalPrefix.call none _ _ (by intro name same; cases same)
    | exact Input.LocalPrefix.call (some (ofString "res")) _ _ (by intro name same; have equal:=Option.some.inj same; subst name; decide)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_body_safe

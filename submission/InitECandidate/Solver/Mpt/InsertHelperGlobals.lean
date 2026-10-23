import InitECandidate.Solver.Mpt.NodeConstructorGlobals
import InitECandidate.Solver.Mpt.CommonPrefixNormal
import InitECandidate.Solver.Mpt.TwoLeavesProgram
import InitECandidate.Solver.Mpt.SplitExtensionProgram
import InitECandidate.Solver.Mpt.LeafUpdateProgram
import InitECandidate.Solver.Mpt.NodeInvalidate
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.MutableTable.MemeqAnyCall

namespace InitECandidate.Solver.Mpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original comparison preserves every global on every outcome,
including a failed minimum call, byte read or timeout. -/
theorem CommonPrefix.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code CommonPrefix.body := by
  have minimum : Input.GlobalEffects.Preserves key code GasBudget.Minimum.body := by
    simp only [GasBudget.Minimum.body,Guest.guestFn_min,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
    repeat first
      | apply Input.GlobalEffects.sequence
      | apply Input.GlobalEffects.conditional
      | exact Input.GlobalEffects.returned key code _
      | exact Input.GlobalEffects.skip key code
  rw [CommonPrefix.body_shape]
  exact Input.GlobalEffects.scoped_body key code _ .one (ofString "min") _ _ GasBudget.Minimum.formals GasBudget.Minimum.body .one
    (CommonPrefix.minimum_code code installed) minimum
    (Input.GlobalEffects.of_readonly key code _ (CommonPrefix.after_minimum_effects code))

theorem NodeInvalidate.globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code NodeInvalidate.body := by
  rw [NodeInvalidate.body_shape]
  unfold NodeInvalidate.fields FieldStores.program
  repeat first
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _

set_option maxRecDepth 100000 in
/-- The actual two-leaf split may allocate nodes, but changes no global
other than heap_ptr, for successful and unsuccessful outcomes alike. -/
theorem TwoLeaves.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code TwoLeaves.body := by
  simp only [TwoLeaves.body,Guest.guestFn__create_branch_from_two_leaves,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "node_new_branch") _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one
        (NodeConstructor.original_code .branch code installed) (NodeConstructor.globals .branch key code installed other)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "node_new_leaf") _ _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed other)

set_option maxRecDepth 100000 in
/-- Both matching-leaf replacement and actual splitting retain scratch,
frame and all other nonheap globals, including on failures. -/
theorem InsertLeaf.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code InsertLeaf.body := by
  simp only [InsertLeaf.body,Guest.guestFn__insert_into_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "memeq") _ _ Memeq32.formals Memeq32.body .one
        (MutableTable.MemeqAny.original_code code installed)
        (Input.GlobalEffects.of_readonly key code _ (MutableTable.MemeqAny.readonly code))
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "common_prefix_length") _ _ CommonPrefix.formals CommonPrefix.body .one
        (CommonPrefix.original_code code installed) (CommonPrefix.globals key code installed)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "_create_branch_from_two_leaves") _ _ TwoLeaves.formals TwoLeaves.body .one
        (TwoLeaves.original_code code installed) (TwoLeaves.globals key code installed other)
    | exact Input.GlobalEffects.call_body key code none (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed other)

set_option maxRecDepth 100000 in
theorem SplitExtension.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code SplitExtension.body := by
  simp only [SplitExtension.body,Guest.guestFn__split_extension,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "node_new_branch") _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one
        (NodeConstructor.original_code .branch code installed) (NodeConstructor.globals .branch key code installed other)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "node_new_ext") _ _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed other)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "node_new_leaf") _ _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed other)

end InitECandidate.Solver.Mpt

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.globals
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.globals
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.globals
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.globals
#print axioms InitECandidate.Solver.Mpt.SplitExtension.globals

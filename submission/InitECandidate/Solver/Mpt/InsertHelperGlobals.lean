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

theorem CommonPrefix.normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code CommonPrefix.body :=
  Input.NormalHeapEffects.of_global code CommonPrefix.body (CommonPrefix.globals (ofString "heap_ptr") code installed)

theorem NodeInvalidate.normal_heap (code) : Input.NormalHeapEffects.Preserves code NodeInvalidate.body :=
  Input.NormalHeapEffects.of_global code NodeInvalidate.body (NodeInvalidate.globals (ofString "heap_ptr") code)

theorem Fail.normal_heap (code) : Input.NormalHeapEffects.Preserves code Fail.body :=
  Input.NormalHeapEffects.of_global code Fail.body
    (Input.GlobalEffects.of_readonly (ofString "heap_ptr") code _ (Fail.readonly code))

set_option maxRecDepth 100000 in
theorem TwoLeaves.normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code TwoLeaves.body := by
  simp only [TwoLeaves.body,Guest.guestFn__create_branch_from_two_leaves,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.NormalHeapEffects.sequence
    | apply Input.NormalHeapEffects.conditional
    | exact Input.NormalHeapEffects.store code _ _
    | exact Input.NormalHeapEffects.returned code _
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "node_new_branch") _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one
        (NodeConstructor.original_code .branch code installed) (NodeConstructor.normal_heap .branch code installed).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "node_new_leaf") _ _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.normal_heap .leaf code installed).returning

set_option maxRecDepth 100000 in
theorem InsertLeaf.normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code InsertLeaf.body := by
  simp only [InsertLeaf.body,Guest.guestFn__insert_into_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.NormalHeapEffects.declared
    | apply Input.NormalHeapEffects.sequence
    | apply Input.NormalHeapEffects.conditional
    | exact Input.NormalHeapEffects.store code _ _
    | exact Input.NormalHeapEffects.returned code _
    | exact Input.NormalHeapEffects.skip code
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "memeq") _ _ Memeq32.formals Memeq32.body .one
        (MutableTable.MemeqAny.original_code code installed)
        (Input.NormalHeapEffects.of_global code _ (Input.GlobalEffects.of_readonly (ofString "heap_ptr") code _ (MutableTable.MemeqAny.readonly code))).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "common_prefix_length") _ _ CommonPrefix.formals CommonPrefix.body .one
        (CommonPrefix.original_code code installed) (CommonPrefix.normal_heap code installed).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "_create_branch_from_two_leaves") _ _ TwoLeaves.formals TwoLeaves.body .one
        (TwoLeaves.original_code code installed) (TwoLeaves.normal_heap code installed).returning
    | exact Input.NormalHeapEffects.call_body code none (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.normal_heap .extension code installed).returning (by trivial)

set_option maxRecDepth 100000 in
theorem SplitExtension.normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code SplitExtension.body := by
  simp only [SplitExtension.body,Guest.guestFn__split_extension,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.NormalHeapEffects.declared
    | apply Input.NormalHeapEffects.sequence
    | apply Input.NormalHeapEffects.conditional
    | exact Input.NormalHeapEffects.store code _ _
    | exact Input.NormalHeapEffects.returned code _
    | exact Input.NormalHeapEffects.skip code
    | exact Input.NormalHeapEffects.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Fail.normal_heap code).returning (by trivial)
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "node_new_branch") _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one
        (NodeConstructor.original_code .branch code installed) (NodeConstructor.normal_heap .branch code installed).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "node_new_ext") _ _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.normal_heap .extension code installed).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "node_new_leaf") _ _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.normal_heap .leaf code installed).returning

end InitECandidate.Solver.Mpt

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.globals
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.globals
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.globals
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.globals
#print axioms InitECandidate.Solver.Mpt.SplitExtension.globals

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.normal_heap

#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.normal_heap

#print axioms InitECandidate.Solver.Mpt.Fail.normal_heap

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.normal_heap

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.normal_heap

#print axioms InitECandidate.Solver.Mpt.SplitExtension.normal_heap

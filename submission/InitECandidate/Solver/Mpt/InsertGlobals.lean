import InitECandidate.Solver.Mpt.InsertProgram
import InitECandidate.Solver.Mpt.InsertHelperGlobals
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
/-- Every outcome of original251 retains all nonheap globals. The real
looked-up constructor, comparison, split and invalidation bodies supply
their frames; no successful helper execution is presumed. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "node_invalidate") _ NodeInvalidate.formals NodeInvalidate.body .one
        (NodeInvalidate.original_code code installed) (NodeInvalidate.globals key code)
    | exact Input.GlobalEffects.call_body key code (some (some (ofString "r"))) (ofString "node_new_leaf") _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed other)
    | exact Input.GlobalEffects.call_body key code (some (some (ofString "r"))) (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed other)
    | exact Input.GlobalEffects.call_body key code (some (some (ofString "r"))) (ofString "_insert_into_leaf") _ InsertLeaf.formals InsertLeaf.body .one
        (InsertLeaf.original_code code installed) (InsertLeaf.globals key code installed other)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "common_prefix_length") _ _ CommonPrefix.formals CommonPrefix.body .one
        (CommonPrefix.original_code code installed) (CommonPrefix.globals key code installed)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "_split_extension") _ _ SplitExtension.formals SplitExtension.body .one
        (SplitExtension.original_code code installed) (SplitExtension.globals key code installed other)

theorem heap_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : Input.OriginalCode.Installed source.code) :
    HeapGlobals source (evaluateHOLFiniteState source body).2 := by
  intro key other
  exact congrArg Prod.snd (globals key source.code installed other source rfl)

set_option maxRecDepth 100000 in
/-- Every actual resuming insertion retains the bounded aligned heap and its
incoming lower frontier through the real allocating helper graph. -/
theorem normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code body := by
  simp only [body,Guest.guestFn__mpt_insert_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat first
    | apply Input.NormalHeapEffects.declared
    | apply Input.NormalHeapEffects.sequence
    | apply Input.NormalHeapEffects.conditional
    | apply Input.NormalHeapEffects.loop
    | exact Input.NormalHeapEffects.assign code _ _
    | exact Input.NormalHeapEffects.store code _ _
    | exact Input.NormalHeapEffects.returned code _
    | exact Input.NormalHeapEffects.skip code
    | exact Input.NormalHeapEffects.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Fail.normal_heap code).returning (by trivial)
    | exact Input.NormalHeapEffects.call_body code (some none) (ofString "node_invalidate") _ NodeInvalidate.formals NodeInvalidate.body .one
        (NodeInvalidate.original_code code installed) (NodeInvalidate.normal_heap code).returning (by trivial)
    | exact Input.NormalHeapEffects.call_body code (some (some (.local,ofString "r"))) (ofString "node_new_leaf") _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.normal_heap .leaf code installed).returning (by trivial)
    | exact Input.NormalHeapEffects.call_body code (some (some (.local,ofString "r"))) (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.normal_heap .extension code installed).returning (by trivial)
    | exact Input.NormalHeapEffects.call_body code (some (some (.local,ofString "r"))) (ofString "_insert_into_leaf") _ InsertLeaf.formals InsertLeaf.body .one
        (InsertLeaf.original_code code installed) (InsertLeaf.normal_heap code installed).returning (by trivial)
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "common_prefix_length") _ _ CommonPrefix.formals CommonPrefix.body .one
        (CommonPrefix.original_code code installed) (CommonPrefix.normal_heap code installed).returning
    | apply Input.NormalHeapEffects.scoped_body code _ .one (ofString "_split_extension") _ _ SplitExtension.formals SplitExtension.body .one
        (SplitExtension.original_code code installed) (SplitExtension.normal_heap code installed).returning

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.globals
#print axioms InitECandidate.Solver.Mpt.Insert.heap_globals

#print axioms InitECandidate.Solver.Mpt.Insert.normal_heap

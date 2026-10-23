import InitECandidate.Solver.Mpt.NibblesConcatGlobals
import InitECandidate.Solver.Mpt.NodeConstructorGlobals
import InitECandidate.Solver.Mpt.DeleteExtensionProgram
import InitECandidate.Solver.Mpt.CollapseBranchProgram
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem DeleteExtension.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code DeleteExtension.body := by
  simp only [DeleteExtension.body,Guest.guestFn__delete_ext_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "nibbles_concat") _ _ NibblesConcat.formals NibblesConcat.body .one
        (NibblesConcat.original_code code installed) (NibblesConcat.globals key code installed other)
    | exact Input.GlobalEffects.call_body key code none (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed other)
    | exact Input.GlobalEffects.call_body key code none (ofString "node_new_leaf") _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed other)

set_option maxRecDepth 100000 in
theorem CollapseBranch.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code CollapseBranch.body := by
  simp only [CollapseBranch.body,Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.store_byte key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply Input.GlobalEffects.scoped_body key code _ .one (ofString "nibbles_concat") _ _ NibblesConcat.formals NibblesConcat.body .one
        (NibblesConcat.original_code code installed) (NibblesConcat.globals key code installed other)
    | exact Input.GlobalEffects.call_body key code none (ofString "node_new_ext") _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed other)
    | exact Input.GlobalEffects.call_body key code none (ofString "node_new_leaf") _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed other)

end InitECandidate.Solver.Mpt

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.globals
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.globals

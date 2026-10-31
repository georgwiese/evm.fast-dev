import InitECandidate.Solver.Mpt.WitnessDecodeProgram
import InitECandidate.Solver.Mpt.NodeConstructorGlobals
import InitECandidate.Solver.Mpt.CompactToNibblesGlobals
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Rlp.SlicesGlobals
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
/-- Every original decode outcome preserves all globals except its actual
persistent heap and scratch cursor updates, including caught failures. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code (WitnessStep.body .decode) := by
  have failCall (arguments : List (ExpHOL 64)) : Input.GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "mpt_fail") arguments):=
    Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") arguments Fail.formals Fail.body .one
      (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
  simp only [WitnessStep.body,WitnessStep.original,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat' first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact failCall _
    | apply Input.GlobalEffects.caught_destination key code (some (ofString "it")) (ofString "rlp_decode_fully") _ Rlp.Header.formals Rlp.Decode.body Rlp.Item.resultShape
        (ofString "RlpErr") (ofString "e") _ (Rlp.Decode.original_code code installed) (Rlp.Decode.globals key code installed notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") _ _ Rlp.Header.formals Rlp.Slices.body Rlp.Slices.resultShape
        (Rlp.Slices.original_code code installed) (Rlp.Slices.globals key code installed notHeap notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "pi") Rlp.Item.resultShape (ofString "rlp_item") _ _ Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape
        (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "cn") CompactToNibbles.resultShape (ofString "compact_to_nibbles") _ _ CompactToNibbles.formals CompactToNibbles.body CompactToNibbles.resultShape
        (CompactToNibbles.original_code code installed) (CompactToNibbles.globals key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "vi") Rlp.Item.resultShape (ofString "rlp_item") _ _ Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape
        (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "lf") .one (ofString "node_new_leaf") _ _ (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one
        (NodeConstructor.original_code .leaf code installed) (NodeConstructor.globals .leaf key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "br") .one (ofString "node_new_branch") _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one
        (NodeConstructor.original_code .branch code installed) (NodeConstructor.globals .branch key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "rec") .one (ofString "scratch_alloc") _ _ Arenas.formals (Arenas.body .down) .one
        (Arenas.original_code code installed .down) (Arenas.globals key code installed .down notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "rec2") .one (ofString "scratch_alloc") _ _ Arenas.formals (Arenas.body .down) .one
        (Arenas.original_code code installed .down) (Arenas.globals key code installed .down notScratch)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.globals

import InitECandidate.Solver.Mpt.WitnessDecodeGlobals
import InitECandidate.Solver.Mpt.WitnessMaterializeWrapperProgram
import InitECandidate.Solver.Mpt.WitnessCoreProgram
import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyCost
import InitECandidate.Solver.MutableTable.NodeDbEnvironment

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) : Input.GlobalEffects.Preserves key code body := by
  apply Input.GlobalEffects.of_readonly
  intro current codeEq
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
  exact WitnessBuild.Database.any_body_readonly current currentInstalled current rfl

end InitECandidate.Solver.MutableTable.NodeDb

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code (WitnessStep.body .resolve) := by
  simp only [WitnessStep.body,WitnessStep.original,Guest.guestFn__resolve_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
    | apply Input.GlobalEffects.caught_destination key code (some (ofString "it")) (ofString "rlp_item") _ Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape
        (ofString "RlpErr") (ofString "e") _ (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "r") MutableTable.NodeDb.resultShape (ofString "nodedb_lookup") _ _ MutableTable.NodeDb.formals MutableTable.NodeDb.body MutableTable.NodeDb.resultShape
        (MutableTable.NodeDb.original_code code installed) (MutableTable.NodeDb.globals key code installed)
    | apply Input.GlobalEffects.scoped_body key code (ofString "hn") .one (ofString "node_new_hashed") _ _ (NodeConstructor.formals .hashed) (NodeConstructor.body .hashed) .one
        (NodeConstructor.original_code .hashed code installed) (NodeConstructor.globals .hashed key code installed notHeap)

end InitECandidate.Solver.Mpt.WitnessResolve

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") : Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
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
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code (ofString "d") (WitnessStep.resultShape .decode) (ofString "_decode_step") _ _ WitnessStep.formals (WitnessStep.body .decode) (WitnessStep.resultShape .decode)
        (WitnessStep.original_code .decode code installed) (WitnessDecode.globals key code installed notHeap notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "r") (WitnessStep.resultShape .resolve) (ofString "_resolve_step") _ _ WitnessStep.formals (WitnessStep.body .resolve) (WitnessStep.resultShape .resolve)
        (WitnessStep.original_code .resolve code installed) (WitnessResolve.globals key code installed notHeap notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "ex") .one (ofString "node_new_ext") _ _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.globals .extension key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "bv") Rlp.Item.resultShape (ofString "rlp_item") _ _ Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape
        (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed notScratch)

end InitECandidate.Solver.Mpt.WitnessCore

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") : Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn__decode_witness_node_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.raised key code _ _
    | apply Input.GlobalEffects.caught_destination key code (some (ofString "nd")) (ofString "_decode_witness_node_body") _ WitnessCore.formals WitnessCore.body .one
        (ofString "MptErr") (ofString "e") _ (WitnessCore.original_code code installed) (WitnessCore.globals key code installed notHeap notScratch)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "scratch_release") _ Arenas.Scratch.formals Arenas.Scratch.releaseBody .one
        (Arenas.Scratch.release_code code installed) (Arenas.Scratch.release_globals key code notScratch)

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") : Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn__decode_witness_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.raised key code _ _
    | apply Input.GlobalEffects.scoped_body key code (ofString "mark") .one (ofString "scratch_mark") _ _ [] (Arenas.markBody .down) .one
        (Arenas.Scratch.mark_code code installed) (Arenas.mark_globals key code .down)
    | apply Input.GlobalEffects.caught_destination key code (some (ofString "nd")) (ofString "_decode_witness_node_mpt") _ WitnessMaterializeMpt.formals WitnessMaterializeMpt.body .one
        (ofString "RlpErr") (ofString "e") _ (WitnessMaterializeMpt.original_code code installed) (WitnessMaterializeMpt.globals key code installed notHeap notScratch)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "scratch_release") _ Arenas.Scratch.formals Arenas.Scratch.releaseBody .one
        (Arenas.Scratch.release_code code installed) (Arenas.Scratch.release_globals key code notScratch)

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.MutableTable.NodeDb.globals
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.globals
#print axioms InitECandidate.Solver.Mpt.WitnessCore.globals
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.globals
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.globals

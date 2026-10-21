import InitECandidate.Solver.Mpt.WitnessMaterializerGlobals
import InitECandidate.Solver.Mpt.WitnessRootPrefixNormal
import InitECandidate.Solver.Input.GlobalByteEffects

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang

set_option maxRecDepth 100000 in
theorem globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Copy32.body := by
  simp only [Copy32.body,Guest.guestFn_memcpy,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.byte_store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code

end InitECandidate.Solver.WitnessRadix.CopyGeneral

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
/-- Every actual original root decoder outcome retains all nonallocator
globals, including ws and bs. Failure/timeout paths are included. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") : Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn_decode_witness_to_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | apply Input.GlobalEffects.scoped_body key code (ofString "is_empty") .one (ofString "memeq") _ _ Memeq32.formals Memeq32.body .one
        (MutableTable.MemeqAny.original_code code installed) (Input.GlobalEffects.of_readonly key code Memeq32.body (MutableTable.MemeqAny.readonly code))
    | apply Input.GlobalEffects.scoped_body key code (ofString "r") MutableTable.NodeDb.resultShape (ofString "nodedb_lookup") _ _ MutableTable.NodeDb.formals MutableTable.NodeDb.body MutableTable.NodeDb.resultShape
        (MutableTable.NodeDb.original_code code installed) (MutableTable.NodeDb.globals key code installed)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code (ofString "nd") .one (ofString "_decode_witness_node") _ _ WitnessMaterialize.formals WitnessMaterialize.body .one
        (WitnessMaterialize.original_code code installed) (WitnessMaterialize.globals key code installed notHeap notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "h") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one
        (CopyGeneral.original_code code installed) (CopyGeneral.globals key code)

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.globals
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.globals

import InitECandidate.Solver.Mpt.CompactToNibblesProgram
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
/-- Original compact-path conversion preserves the current scratch/frame
cursors and every global except the genuine persistent allocator cursor. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.Software.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat' first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.byte_store key code _ _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
    | apply Input.GlobalEffects.scoped_body key code (ofString "out") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "key_to_nibbles") _ KeyToNibbles.formals KeyToNibbles.body .one
        (KeyToNibbles.original_code code installed) (KeyToNibbles.all_globals key code)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.globals

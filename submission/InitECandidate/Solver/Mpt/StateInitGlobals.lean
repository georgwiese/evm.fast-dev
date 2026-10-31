import InitECandidate.Solver.Mpt.WitnessRootGlobals
import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.Input.CurrentTable.NewCost
import InitECandidate.Solver.Input.GlobalEffectsGlobalCall

namespace InitECandidate.Solver.Mpt.StateInitGlobals
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def changed : List MlS := [ofString "bs", ofString "heap_ptr", ofString "journal", ofString "journal_cap", ofString "journal_n", ofString "scratch_ptr", ofString "sk_buf", ofString "ts", ofString "ws"]

set_option maxRecDepth 100000 in
/-- The current Patricia constructor only changes the persistent heap
pointer. Its four actual allocations and every failure outcome are included. -/
theorem preserves_htab_new (key : MlS) (code) (installed : OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code CurrentTable.New.body := by
  simp only [CurrentTable.New.body,Guest.Software.guestFn_htab_new,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.scoped_body key code _ .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)

set_option maxRecDepth 100000 in
/-- Reuse the checked current root decoder and Patricia constructor effects
rather than duplicate their entire transitive helper graph. -/
theorem preserves_state_init (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code StateInit.body := by
  have notHeap : key≠ofString "heap_ptr":=by intro same; apply safe; rw [same]; decide
  have notScratch : key≠ofString "scratch_ptr":=by intro same; apply safe; rw [same]; decide
  simp only [StateInit.body,Guest.Software.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | apply GlobalEffects.global_other key code _ _ (by intro same; apply safe; rw [same]; decide)
    | apply GlobalEffects.global_call_body key code _ (ofString "alloc") _ PersistentAlloc.formals PersistentAlloc.body .one
        (by intro same; apply safe; rw [same]; decide) (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)
    | apply GlobalEffects.scoped_body key code _ .one (ofString "decode_witness_to_mpt") _ _ WitnessDecodeRoot.formals WitnessDecodeRoot.body .one
        (WitnessDecodeRoot.original_code code installed) (WitnessDecodeRoot.globals key code installed notHeap notScratch)
    | apply GlobalEffects.scoped_body key code _ .one (ofString "htab_new") _ _ CurrentTable.New.formals CurrentTable.New.body .one
        (CurrentTable.New.original_code code installed) (preserves_htab_new key code installed notHeap)
    | exact GlobalEffects.call_body key code (some (some _)) (ofString "htab_new") _ CurrentTable.New.formals CurrentTable.New.body .one
        (CurrentTable.New.original_code code installed) (preserves_htab_new key code installed notHeap)

end InitECandidate.Solver.Mpt.StateInitGlobals

#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_htab_new
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_state_init

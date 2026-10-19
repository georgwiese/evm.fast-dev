import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Mpt.WsAccountLeafAllocCost
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Mpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem KeyToNibbles.globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code KeyToNibbles.body := by
  simp only [KeyToNibbles.body,Guest.guestFn_key_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store_byte key code _ _
    | exact Input.GlobalEffects.returned key code _

theorem TrieLookup.globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code TrieLookup.body := by
  rw [TrieLookup.body_shape]
  unfold TrieLookup.prepare TrieLookup.forward
  exact Input.GlobalEffects.sequence key code _ _
    (Input.GlobalEffects.call_body key code (some none) (ofString "key_to_nibbles") _ KeyToNibbles.formals KeyToNibbles.body .one
      (KeyToNibbles.original_code code installed) (KeyToNibbles.globals key code))
    (Input.GlobalEffects.call_body key code none (ofString "trie_walk") _ TrieWalk.formals TrieWalk.body TrieWalk.resultShape
      (TrieWalk.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (TrieWalk.readonly code installed)))

theorem permutation_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak_f1600")=some (Keccak.formals,Keccak.f1600Body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 90 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak_f1600) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Keccak.formals,Keccak.f1600Body,
    Guest.guestFn_keccak_f1600,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem absorb_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak_absorb_block")=some (KeccakAbsorb.formals,KeccakAbsorb.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 91 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak_absorb_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,KeccakAbsorb.formals,KeccakAbsorb.body,
    Guest.guestFn_keccak_absorb_block,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Even exceptional/timeout account-leaf executions preserve both arena
cursors and every other global except the temporary heap cursor. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterMark afterAlloc hash lookup finish
  have hashPure := Keccak256.globals key code (Zero.original_code code installed) (GasBudget.Mcopy.copy_code code installed)
    (absorb_code code installed) (permutation_code code installed)
  have markPure : Input.GlobalEffects.Preserves key code Input.HeapScope.markBody := by
    rw [Input.HeapScope.mark_shape]
    exact Input.GlobalEffects.returned key code _
  have releasePure : Input.GlobalEffects.Preserves key code Input.HeapScope.releaseBody := by
    rw [Input.HeapScope.release_shape]
    exact Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.global_other key code _ _ other) (Input.GlobalEffects.returned key code _)
  repeat first
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code (ofString "mark") .one (ofString "heap_mark") _ _ [] Input.HeapScope.markBody .one
        (Input.HeapScope.mark_original_code code installed) markPure
    | apply Input.GlobalEffects.scoped_body key code (ofString "h") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (alloc_original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply Input.GlobalEffects.scoped_body key code (ofString "r") TrieWalk.resultShape (ofString "trie_lookup") _ _ TrieLookup.formals TrieLookup.body TrieWalk.resultShape
        (TrieLookup.original_code code installed) (TrieLookup.globals key code installed)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "keccak256") _ Keccak256.formals Keccak256.body .one
        (hash_original_code code installed) hashPure
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "heap_release") _ Input.HeapScope.releaseFormals Input.HeapScope.releaseBody .one
        (Input.HeapScope.release_original_code code installed) releasePure

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.globals
#print axioms InitECandidate.Solver.Mpt.TrieLookup.globals
#print axioms InitECandidate.Solver.Mpt.permutation_code
#print axioms InitECandidate.Solver.Mpt.absorb_code
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.globals
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.globals

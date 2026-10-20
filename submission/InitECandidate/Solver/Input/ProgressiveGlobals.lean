import InitECandidate.Solver.Input.ProgressiveProgram

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] GlobalEffects.Preserves

/-- All real original progressive outcomes retain initialized nonheap
pointers/globals, including escaping errors, exceptions and FFI outcomes. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn_merkleize_progressive,progToHOL,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.declared
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ _ _ _ (CopyGeneral.original_code code installed) (Copy32.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "memzero") _ _ _ _ (Zero.original_code code installed) (Zero.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_pair") _ _ _ _ (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "merkleize") _ _ _ _ (Merkle.original_code code installed) (Merkle.globals key code installed other)
    | exact GlobalEffects.call_body key code (some none) (ofString "heap_release") _ _ _ _ (HeapScope.release_original_code code installed) (Merkle.release_globals key code other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.globals

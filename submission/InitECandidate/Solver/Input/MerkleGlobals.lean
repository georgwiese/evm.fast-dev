import InitECandidate.Solver.Input.MerkleBodyCost
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] GlobalEffects.Preserves

theorem logarithm_globals (key : MlS) (code) : GlobalEffects.Preserves key code CeilLog2.body := by
  simp only [CeilLog2.body,Guest.guestFn_ceil_log2,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.declared
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.returned key code _

theorem maximum_globals (key : MlS) (code) : GlobalEffects.Preserves key code UnsignedMax.body := by
  rw [UnsignedMax.body_shape]
  unfold UnsignedMax.guard
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _

theorem mark_globals (key : MlS) (code) : GlobalEffects.Preserves key code HeapScope.markBody := by
  rw [HeapScope.mark_shape]
  exact GlobalEffects.returned key code _

theorem release_globals (key : MlS) (code) (other : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code HeapScope.releaseBody := by
  rw [HeapScope.release_shape]
  exact GlobalEffects.sequence key code _ _ (GlobalEffects.global_other key code _ _ other) (GlobalEffects.returned key code _)

/-- All original Merkle outcomes preserve every global except the actual
heap cursor. In particular the initialized SHA and zero-table pointers
survive without assumptions about hash contents or successful returns. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code body := by
  simp only [body,Guest.guestFn_merkleize,progToHOL,Option.map_none]
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
    | exact GlobalEffects.call_body key code (some none) (ofString "heap_release") _ _ _ _ (HeapScope.release_original_code code installed) (release_globals key code other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ceil_log2") _ _ _ _ _ (CeilLog2.original_code code installed) (logarithm_globals key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "max") _ _ _ _ _ (UnsignedMax.original_code code installed) (maximum_globals key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (mark_globals key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.logarithm_globals
#print axioms InitECandidate.Solver.Input.Merkle.maximum_globals
#print axioms InitECandidate.Solver.Input.Merkle.mark_globals
#print axioms InitECandidate.Solver.Input.Merkle.release_globals
#print axioms InitECandidate.Solver.Input.Merkle.globals

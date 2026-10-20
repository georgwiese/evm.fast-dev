import InitECandidate.Solver.Input.PContainerBitLoop

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem suffix_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code afterProgressive := by
  rw [body_shape.2.2.2.1,body_shape.2.2.2.2.1,body_shape.2.2.2.2.2.1,body_shape.2.2.2.2.2.2.1,body_shape.2.2.2.2.2.2.2.2.2]
  apply GlobalEffects.declared key code
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code code installed) (Zero.globals key code))
    (GlobalEffects.declared key code _ _ _ _
      (GlobalEffects.sequence key code _ _ (bit_loop_globals key code)
        (GlobalEffects.sequence key code _ _
          (GlobalEffects.call_body key code (some none) (ofString "sha256_pair") shaArguments ShaFixedCost.pairFormals ShaFixedCost.pairBody .one
            (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed))
          (GlobalEffects.sequence key code _ _
            (GlobalEffects.call_body key code (some none) (ofString "heap_release") [WitnessRadix.QueryBranch.localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
              (HeapScope.release_original_code code installed) (Merkle.release_globals key code different))
            (GlobalEffects.returned key code _)))))

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape.1,body_shape.2.1,body_shape.2.2.1]
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different)
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "merkleize_progressive") progressiveArguments Progressive.formals Progressive.body .one
      (Progressive.original_code code installed) (Progressive.globals key code installed different))
    (suffix_globals key code installed different)

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.suffix_globals
#print axioms InitECandidate.Solver.Input.PContainer.globals

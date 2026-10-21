import InitECandidate.Solver.Input.RequestRootHashReady

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem phase_globals (phase : Phase) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code phase.call := by
  cases phase with
  | payload=>exact GlobalEffects.call_body key code (some none) (ofString "htr_payload") _ PayloadHash.formals PayloadHash.body .one (PayloadHash.original_code code installed) (PayloadHash.globals key code installed different)
  | blobs=>exact GlobalEffects.call_body key code (some none) (ofString "htr_plist_chunks") _ PListChunks.formals PListChunks.body .one (PListChunks.original_code code installed) (PListChunks.globals key code installed different)
  | parent=>exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code)
  | requests=>exact GlobalEffects.call_body key code (some none) (ofString "htr_requests") _ RequestsHash.formals RequestsHash.body .one (RequestsHash.original_code code installed) (RequestsHash.globals key code installed different)
  | root=>exact GlobalEffects.call_body key code (some none) (ofString "merkleize") _ Merkle.formals Merkle.body .one (Merkle.original_code code installed) (Merkle.globals key code installed different)

theorem pipeline_globals (phases : List Phase) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code (pipeline phases) := by
  induction phases with
  | nil=>
    exact GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") _ HeapScope.releaseFormals HeapScope.releaseBody .one (HeapScope.release_original_code code installed) (Merkle.release_globals key code different))
      (GlobalEffects.returned key code _)
  | cons phase rest ih=>exact GlobalEffects.sequence key code _ _ (phase_globals phase key code installed different) ih

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  exact GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different) (pipeline_globals phases key code installed different)

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_globals
#print axioms InitECandidate.Solver.Input.RequestRootHash.pipeline_globals
#print axioms InitECandidate.Solver.Input.RequestRootHash.globals

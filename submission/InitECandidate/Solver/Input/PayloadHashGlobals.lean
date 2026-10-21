import InitECandidate.Solver.Input.PayloadHashBody

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole original payload hash changes no global except its actual heap
cursor, on every outcome; helper contracts are for the original code. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  have release (arguments : List (ExpHOL 64)) := GlobalEffects.call_body key code (some none) (ofString "heap_release") arguments HeapScope.releaseFormals HeapScope.releaseBody .one
    (HeapScope.release_original_code code installed) (Merkle.release_globals key code different)
  have container := GlobalEffects.call_body key code (some none) (ofString "htr_pcontainer") StaticFields.containerArguments PContainer.formals PContainer.body .one
    (PContainer.original_code code installed) (PContainer.globals key code installed different)
  have balance := GlobalEffects.call_body key code (some none) (ofString "htr_pbytes") StaticFields.balanceArguments PBytes.formals PBytes.body .one
    (PBytes.original_code code installed) (PBytes.globals key code installed different)
  have list (arguments : List (ExpHOL 64)) := GlobalEffects.call_body key code (some none) (ofString "htr_plist_chunks") arguments PListChunks.formals PListChunks.body .one
    (PListChunks.original_code code installed) (PListChunks.globals key code installed different)
  have final : GlobalEffects.Preserves key code finalFields := by
    rw [StaticFields.final_shape]
    apply StaticFields.program_globals _ _ key code installed different
    exact GlobalEffects.sequence key code _ _ balance
      (GlobalEffects.sequence key code _ _ (StaticFields.step_globals (.scalar 532 18) key code installed different)
        (GlobalEffects.sequence key code _ _ container
          (GlobalEffects.sequence key code _ _ (release _) (GlobalEffects.returned key code _))))
  have withdrawals : GlobalEffects.Preserves key code withdrawalScope := by
    rw [withdrawal_shapes.1,withdrawal_shapes.2.1,withdrawal_shapes.2.2.1,withdrawal_shapes.2.2.2.1,
      withdrawal_shapes.2.2.2.2.1,withdrawal_shapes.2.2.2.2.2.1,withdrawal_shapes.2.2.2.2.2.2]
    apply GlobalEffects.declared key code
    apply GlobalEffects.declared key code
    exact GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some (some (ofString "roots"))) (ofString "alloc") (rootsAllocationArguments "nwd") PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different))
      (GlobalEffects.sequence key code _ _ (GlobalEffects.assign key code _ _)
        (GlobalEffects.sequence key code _ _ (Withdrawals.loop_globals key code installed different)
          (GlobalEffects.sequence key code _ _ (list _) (GlobalEffects.sequence key code _ _ (release _) final))))
  have transactions : GlobalEffects.Preserves key code transactionScope := by
    rw [transaction_shapes.1,transaction_shapes.2.1,transaction_shapes.2.2.1,transaction_shapes.2.2.2.1,
      transaction_shapes.2.2.2.2.1,transaction_shapes.2.2.2.2.2.1,transaction_shapes.2.2.2.2.2.2.1,transaction_shapes.2.2.2.2.2.2.2]
    apply GlobalEffects.declared key code
    apply GlobalEffects.declared key code
    apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
    apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different)
    apply GlobalEffects.declared key code
    exact GlobalEffects.sequence key code _ _ (Transactions.loop_globals key code installed different)
      (GlobalEffects.sequence key code _ _ (list _) (GlobalEffects.sequence key code _ _ (release _) withdrawals))
  have initialGlobals : GlobalEffects.Preserves key code afterChunks := by
    rw [StaticFields.prefix_shape]
    apply StaticFields.program_globals _ _ key code installed different
    exact GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "htr_bytes_list") StaticFields.extraArguments BytesListHash.formals BytesListHash.body .one
        (BytesListHash.original_code code installed) (BytesListHash.globals key code installed different))
      (StaticFields.program_globals _ _ key code installed different transactions)
  rw [entry_shapes.1,entry_shapes.2.1,entry_shapes.2.2]
  apply GlobalEffects.declared key code
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  exact GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different) initialGlobals

end InitECandidate.Solver.Input.PayloadHash
#print axioms InitECandidate.Solver.Input.PayloadHash.globals

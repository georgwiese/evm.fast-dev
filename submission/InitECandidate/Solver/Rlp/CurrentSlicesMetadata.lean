import InitECandidate.Solver.Rlp.SlicesSyntax
import InitECandidate.Solver.Rlp.UncheckedCall
import InitECandidate.Solver.Input.MemoryEffects

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual second pass writes its records but retains every other
runtime field. Its unchecked item reader is readonly on all outcomes. -/
theorem after_alloc_metadata (code) (installed : OriginalCode.Installed code) :
    MemoryEffects.Preserves code afterAlloc := by
  rw [after_alloc_shape,loop_shape]
  apply MemoryEffects.declared
  apply MemoryEffects.declared
  apply MemoryEffects.sequence
  · apply MemoryEffects.loop
    unfold loopBody
    apply MemoryEffects.scoped_body code _ .one (ofString "rlp_item_total_unchecked") _ _ [(ofString "p",.one)] Unchecked.body .one
      (Unchecked.original_code code installed) (MemoryEffects.of_readonly code _ (Unchecked.readonly code installed))
    simp only [Slices.stores,advances]
    exact MemoryEffects.sequence code _ _ (MemoryEffects.store code _ _)
      (MemoryEffects.sequence code _ _ (MemoryEffects.store code _ _)
        (MemoryEffects.sequence code _ _ (MemoryEffects.assign code _ _) (MemoryEffects.assign code _ _)))
  · exact MemoryEffects.returned code _

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.after_alloc_metadata

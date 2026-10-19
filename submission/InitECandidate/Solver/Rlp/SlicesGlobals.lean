import InitECandidate.Solver.Rlp.DecodeGlobals
import InitECandidate.Solver.Rlp.SlicesProgram
import InitECandidate.Solver.Rlp.UncheckedCall
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The original list conversion may update heap/scratch cursors, and
preserves every other global on all actual outcomes. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape,after_count_shape,after_alloc_shape,loop_shape]
  unfold loopBody stores advances
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code (ofString "count") .one (ofString "rlp_list_count") _ _ Header.formals ListCount.body .one
        (ListCount.original_code code installed) (ListCount.globals key code installed notScratch)
    | apply Input.GlobalEffects.scoped_body key code (ofString "arr") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "total") .one (ofString "rlp_item_total_unchecked") _ _ [(ofString "p",.one)] Unchecked.body .one
        (Unchecked.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Unchecked.readonly code installed))

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.globals

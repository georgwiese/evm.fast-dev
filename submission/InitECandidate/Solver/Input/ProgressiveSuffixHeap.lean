import InitECandidate.Solver.Input.ProgressiveDenseCost

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A real normal final fold preserves the saved mark/current heap, then
executes the original copy/release/return suffix to restore that mark. -/
theorem after_zero_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterZeroAcc=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [fold_shape.2.2.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post foldLoop afterFold value
    ((fold_loop_other (ofString "mark") (by decide)).summary_full source).2.1 run
  have summary := (fold_loop_other (ofString "mark") (by decide)).summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (summary.1 rfl).trans saved
  have frame := fold_loop_globals (ofString "heap_ptr") source.code installed source rfl
  rw [normal] at frame
  have nextHeap : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) := (congrArg Prod.snd frame).trans heap
  have fields := evaluation_fields source middle foldLoop none normal
  rw [fold_shape.2.2.2.2.2] at remaining
  exact HeapScope.copy_release_return_heap middle post mark old outputArguments (fields.2.2.2.symm ▸ installed) nextMark nextHeap value remaining

/-- Original accumulator zeroing preserves the saved heap/mark on its real
normal return; the actual final fold restores the mark. -/
theorem suffix_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [fold_shape.2.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterZeroAcc value (safe.summary_full source).2.1 run
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (summary.1 rfl).trans saved
  have global : GlobalEffects.Preserves (ofString "heap_ptr") source.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
    GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code installed) (Zero.globals (ofString "heap_ptr") source.code)
  have frame := global source rfl
  rw [normal] at frame
  have nextHeap : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) := (congrArg Prod.snd frame).trans heap
  have fields := evaluation_fields source middle _ none normal
  exact after_zero_return_heap middle post mark old (fields.2.2.2.symm ▸ installed) nextMark nextHeap value remaining

/-- Actual normal progressive chunk/fold execution restores its saved entry
mark, with the continuing chunk loop deriving the real current heap. -/
theorem dense_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel mark : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) (mapped : Geometry p roots cursor zeros n)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "mark") loop := by
    rw [loop_shape.1]
    exact .loop _ (step_other (ofString "mark") (by decide) (by decide) (by decide) (by decide))
  rw [fold_shape.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post loop afterLoop value (safe.summary_full source).2.1 run
  obtain ⟨nextK,nextBound,next⟩ := loop_normal source middle p roots cursor zeros stp accel n k bounded inside actual mapped normal
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (summary.1 rfl).trans saved
  exact suffix_return_heap middle post mark cursor next.workspace.installed nextMark next.heap value remaining

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.after_zero_return_heap
#print axioms InitECandidate.Solver.Input.Progressive.suffix_return_heap
#print axioms InitECandidate.Solver.Input.Progressive.dense_return_heap

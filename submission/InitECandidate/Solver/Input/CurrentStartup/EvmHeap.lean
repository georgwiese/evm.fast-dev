import InitECandidate.Solver.Input.CurrentStartup.EvmHeapBounds
import InitECandidate.Solver.Input.CurrentStartup.HeapMarks
import InitECandidate.Solver.Input.CallPrefixFrameTrace
import InitECandidate.Solver.Input.NormalHeapPrefix

namespace InitECandidate.Solver.Input.CurrentStartup.EvmHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual EVM initializer returns with its incoming heap frontier
retained. Its temporary allocation and33byte stores preserve the real saved
mark; the genuine release restores that mark before the remaining allocations.
No independent monotonicity assumption is imposed on heap_release. -/
theorem returning (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .evm_init) := by
  intro source codeEq lower initial value returned
  have sourceInstalled : OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  let post := (evaluateHOLFiniteState source (Code.body .evm_init)).2
  have actual : evaluateHOLFiniteState source (CallPrefix.program actions tail) = (some (.returned value), post) := by
    rw [← source_shape]
    exact Prod.ext returned rfl
  have never : NoReturn.Never (CallPrefix.program actions .skip) :=
    CallPrefix.kept_never actions (ofString "unused") (fun action member => List.all_eq_true.mp actions_safe action member)
  obtain ⟨current, inner, execution, tailRun, clock, frame⟩ :=
    CallPrefix.normal_frame_trace source post actions tail value never actual
  have currentHeap := NormalHeapEffects.execution execution (prefix_pure source.code sourceInstalled) lower initial
  have currentInstalled : OriginalCode.Installed current.code := by
    rw [execution.runtime.2.2.2.1]; exact sourceInstalled
  obtain ⟨pointer, heap, low, high, aligned⟩ := initial
  have markedExecution := execution
  rw [head_shape] at markedExecution
  obtain ⟨markedState, first, remaining⟩ := markedExecution.head
  have snapshot := HeapMarks.mark_reached (ofString "mark") pointer sourceInstalled heap first
  have saved : markedState.locals.lookup (ofString "mark") = some (.val (.word pointer)) := by
    rw [snapshot]
    simp [HeapMarks.marked, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have currentMark := (remaining.keeps (ofString "mark")
    (fun action member => List.all_eq_true.mp mark_kept action member)).trans saved
  rw [tail_shape] at tailRun
  have safe : LocalPrefix (ofString "mark") release :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨released, releaseRun, suffixRun, savedAgain⟩ := safe.normal_continue current inner afterRelease value tailRun
  have releasedHeap := HeapMarks.release_lower current released lower pointer currentInstalled currentHeap currentMark low high aligned releaseRun
  have releasedInstalled : OriginalCode.Installed released.code := by
    rw [(evaluation_fields current released release none releaseRun).2.2.2]; exact currentInstalled
  have suffixHeap := suffix_pure released.code releasedInstalled released rfl lower releasedHeap (by rw [suffixRun]; trivial)
  rw [suffixRun] at suffixHeap
  exact NormalHeapEffects.of_erase inner post lower frame.symm suffixHeap

end InitECandidate.Solver.Input.CurrentStartup.EvmHeap

#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.returning

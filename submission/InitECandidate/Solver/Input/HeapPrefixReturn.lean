import InitECandidate.Solver.Input.HeapReleaseReturn
import InitECandidate.Solver.Input.GlobalEffects

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Transport a genuine heap-restoring return through a reached prefix
that preserves its saved mark and current heap. Errors never resume it. -/
theorem sequence_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (first second : ProgHOL 64) (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (safe : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "mark") first current)
    (pure : GlobalEffects.Preserves (ofString "heap_ptr") source.code first)
    (tail : ∀ middle : PanSemStateFiniteExact 64 Guest.HostMemory,OriginalCode.Installed middle.code →
      middle.locals.lookup (ofString "mark")=some (.val (.word mark)) →
      middle.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) → ∀ value,
      evaluateHOLFiniteState middle second=(some (.returned value),post) →
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq first second)=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post first second value (safe source).2.1 run
  have summary := safe source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark := (summary.1 rfl).trans saved
  have frame := pure source rfl
  rw [normal] at frame
  have nextHeap := (congrArg Prod.snd frame).trans heap
  have fields := evaluation_fields source middle first none normal
  exact tail middle (fields.2.2.2.symm ▸ installed) nextMark nextHeap value remaining

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.sequence_return_heap

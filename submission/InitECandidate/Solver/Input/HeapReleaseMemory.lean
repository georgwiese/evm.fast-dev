import InitECandidate.Solver.Input.MemoryBodyCall
import InitECandidate.Solver.Input.HeapScopeCost

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem release_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source releaseBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [release_shape] at run
  have safe : LocalPrefix (ofString "marker") (.assign .global (ofString "heap_ptr") (localVar "m")) := .globalAssign _ _
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (.return (.const 0#64)) value (safe.summary_full source).2.1 run
  have front := MemoryAt.assign_current source .global (ofString "heap_ptr") (localVar "m") query
  rw [normal] at front
  have tail := MemoryAt.return_current middle (.const 0#64) query
  rw [remaining] at tail
  exact tail.trans front

/-- Real normal heap_release modifies no memory, regardless of its actual
saved mark/current heap metadata; argument validity follows from this call. -/
theorem release_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") arguments)=(none,post)) : post.memory query=source.memory query :=
  MemoryAt.call_body_normal source post (ofString "heap_release") arguments releaseFormals releaseBody .one query (release_original_code source.code installed)
    (fun entry target value evaluated=>release_body_memory entry target query value evaluated) run

theorem release_return_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "heap_release") arguments) (.return (.const 0#64)))=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "marker") (.call (some (none,none)) (ofString "heap_release") arguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (.return (.const 0#64)) value (safe.summary_full source).2.1 run
  have front := release_call_memory source middle arguments query installed normal
  have tail := MemoryAt.return_current middle (.const 0#64) query
  rw [remaining] at tail
  exact tail.trans front

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.release_body_memory
#print axioms InitECandidate.Solver.Input.HeapScope.release_call_memory
#print axioms InitECandidate.Solver.Input.HeapScope.release_return_memory

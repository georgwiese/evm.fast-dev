import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.CopyZeroMemoryNormal

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem copy_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (src dst query : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst length) (away : CopyGeneral.Away dst query length)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memcpy") arguments) (.return (.const 0#64)))=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "marker") (.call (some (none,none)) (ofString "memcpy") arguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (.return (.const 0#64)) value (safe.summary_full source).2.1 run
  have front := copy_normal source middle arguments src dst query length args installed domain srcArena dstArena away normal
  have tail := return_current middle (.const 0#64) query
  rw [remaining] at tail
  exact tail.trans front

/-- Actual original copy/release/return suffix preserves a protected word
outside its real destination, without a future release or mark premise. -/
theorem copy_release_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments releaseArgs : List (ExpHOL 64)) (src dst query : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst length) (away : CopyGeneral.Away dst query length)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memcpy") arguments)
      (.seq (.call (some (none,none)) (ofString "heap_release") releaseArgs) (.return (.const 0#64))))=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "marker") (.call (some (none,none)) (ofString "memcpy") arguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 run
  have front := copy_normal source middle arguments src dst query length args installed domain srcArena dstArena away normal
  have fields := evaluation_fields source middle _ none normal
  have tail := HeapScope.release_return_memory middle post releaseArgs query (fields.2.2.2.symm ▸ installed) value remaining
  exact tail.trans front

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.copy_returned
#print axioms InitECandidate.Solver.Input.MemoryAt.copy_release_returned

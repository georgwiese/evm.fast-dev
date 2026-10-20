import InitECandidate.Solver.Input.ProgressiveInitialized
import InitECandidate.Solver.Input.ProgressiveSuffixHeap

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole unchanged progressive Merkle execution: actual heap mark,
roots768/acc32 allocations, geometric chunk loop, final fold, output and
release. All non-timeout outcomes have a linear source-clock bound; a real
normal return restores the actual entry heap cursor. -/
theorem body_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros stp accel : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : ShaPair.Workspace source stp accel)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (temporaryArena : AllocatedBytes.Arena roots (832+64*n)) (aligned : roots.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n+24146 ∧
      (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots))) := by
  rw [allocation_shape.1] at run
  obtain ⟨markPaid,markedFinal,markedRun,markEndpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.installed) result run notTimeout
  let marked := bind {source with clock:=source.clock-1} "mark" roots
  have markedWorkspace := ShaPair.Workspace.of_fields source marked stp accel workspace rfl rfl rfl rfl
  have markedOther (name : String) (different : ofString "mark"≠ofString name) : marked.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name roots different
  have prefixArena := AllocatedBytes.Arena.weaken roots (832+64*n) 800 temporaryArena (by omega)
  obtain ⟨allocationPaid,allocatedFinal,allocatedRun,allocationEndpoint⟩ := allocation_prefix marked markedFinal roots workspace.installed heap prefixArena aligned result markedRun notTimeout
  let entry := initialized marked roots
  have cells := initialized_cells marked roots
  have entryWorkspace := initialized_workspace marked roots stp accel markedWorkspace
  have other (name : String) (a : ofString "roots"≠ofString name) (b : ofString "acc"≠ofString name) (c : ofString "k"≠ofString name)
      (d : ofString "off"≠ofString name) (e : ofString "size"≠ofString name) (f : ofString "mark"≠ofString name) :
      entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (initialized_other marked roots name a b c d e).trans (markedOther name f)
  have entryTable : entry.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) :=
    (initialized_global_other marked roots (ofString "zero_hashes") (by decide)).trans table
  have ready : RoundState entry p roots (temporary roots) zeros stp accel n 0 :=
    ⟨(other "p" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pointer,cells.1,
      (other "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans count,
      cells.2.2.2.1,cells.2.2.2.2,cells.2.2.1,initialized_heap marked roots prefixArena aligned,entryTable,entryWorkspace⟩
  obtain ⟨rootsArena,accArena,bufferArena,accAligned,bufferAligned⟩ := initialized_geometry roots n temporaryArena aligned
  have mapped : Geometry p roots (temporary roots) zeros n := ⟨inputArena,rootsArena,bufferArena,bufferAligned,tableArena⟩
  have denseCost := dense_cost entry allocatedFinal p roots (temporary roots) zeros stp accel (accPointer roots) out n 0 bounded (by decide) ready mapped cells.2.1
    ((other "out" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans output) accArena outputArena accAligned result allocatedRun notTimeout
  have price : entry.clock-allocatedFinal.clock≤115*n+24143 := by simpa [allowance,offset,Nat.add_assoc] using denseCost
  have finalClock := evaluateHOLFiniteState_clock_le entry loopAndSuffix
  rw [allocatedRun] at finalClock
  change allocatedFinal.clock≤entry.clock at finalClock
  have endpointClock : post.clock=allocatedFinal.clock := by rw [markEndpoint,allocationEndpoint]; rfl
  have entryClock : entry.clock=marked.clock-2 := (initialized_frame marked roots).1
  have markedClock : marked.clock=source.clock-1 := rfl
  refine ⟨by rw [endpointClock]; omega,?_⟩
  intro value returned
  have currentRun := allocatedRun
  rw [returned] at currentRun
  have entryMark : entry.locals.lookup (ofString "mark")=some (.val (.word roots)) :=
    (initialized_other marked roots "mark" (by decide) (by decide) (by decide) (by decide) (by decide)).trans (bind_lookup_same _ _ _)
  have restored := dense_return_heap entry allocatedFinal p roots (temporary roots) zeros stp accel roots n 0 bounded (by decide) ready mapped entryMark value currentRun
  rw [markEndpoint,allocationEndpoint]
  exact restored

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.body_summary

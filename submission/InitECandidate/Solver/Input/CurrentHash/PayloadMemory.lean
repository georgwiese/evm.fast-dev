import InitECandidate.Solver.Input.CurrentHash.PayloadPrefixMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadCost
import InitECandidate.Solver.Input.CurrentHash.PayloadHeap

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem Before.after_mark_memory (data : Before input source blob record array cursor chunk out zeros length start size)
    (raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (query : BitVec 64) (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [entry_shapes.2.2] at actual
  obtain ⟨room,funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "ch" [.panop .mul [.const 19#64,.const 32#64]] afterChunks cursor 608#64 rfl
    (PersistentAlloc.original_code source.code data.context.installed) (Trap.original_code source.code data.context.installed) data.context.heap data.context.heapBound value actual
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} cursor 608#64
  let entry := MemoryContextAllocation.entry source cursor 608#64 "ch"
  have next : State input entry blob record array cursor (PersistentAlloc.rounded cursor 608#64) chunk out zeros length start size := data.allocated (post:=allocated) raw room rfl
  have frame := next.prefix_memory (post:=inner) query before chunkAway outAway value remaining
  rw [endpoint]
  exact frame

theorem Before.after_raw_memory (data : Before input source blob record array cursor chunk out zeros length start size)
    (raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (query : BitVec 64) (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterRaw=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [entry_shapes.2.1] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark data.context.heap
    (HeapScope.mark_original_code source.code data.context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have next : Before input entry blob record array cursor chunk out zeros length start size := (data.at_clock (source.clock-1)).bound "mark" cursor (by decide)
  have pointer : entry.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))) :=
    (bind_lookup_other {source with clock:=source.clock-1} "mark" "raw" cursor (by decide)).trans raw
  have frame := next.after_mark_memory (post:=inner) pointer query before chunkAway outAway value remaining
  rw [endpoint]
  exact frame

/-- Complete unchanged current payload body protects earlier metadata outside
its actual output/length chunk and restores the entering heap, on this same
normal return. Actual nested allocations derive their own room and extents. -/
theorem body_frame (data : Before input source blob record array cursor chunk out zeros length start size)
    (query : BitVec 64) (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have heap := body_heap source post cursor data.context.installed data.context.heap value actual
  let entry := bind source "raw" (blob+62#64)
  have next : Before input entry blob record array cursor chunk out zeros length start size := data.bound "raw" (blob+62#64) (by decide)
  let output := evaluateHOLFiniteState entry afterRaw
  have whole := ScalarScope.declare_execute source output.2 "raw" (fieldExpression 0) (blob+62#64) afterRaw output.1 data.raw_read rfl
  rw [←entry_shapes.1] at whole
  have resultEq : some (.returned value)=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have memoryEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.memory query) (actual.symm.trans whole)
  change post.memory query=output.2.memory query at memoryEq
  have returned : evaluateHOLFiniteState entry afterRaw=(some (.returned value),output.2) := Prod.ext resultEq.symm rfl
  have frame := next.after_raw_memory (post:=output.2) (bind_lookup_same source "raw" (blob+62#64)) query before chunkAway outAway value returned
  change output.2.memory query=source.memory query at frame
  exact ⟨memoryEq.trans frame,heap⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.after_raw_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.body_frame

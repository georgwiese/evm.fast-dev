import InitECandidate.Solver.Input.WitnessDecodeArrayTrace
import InitECandidate.Solver.Mpt.WitnessDecodePairCost

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem first_two (items : List Rlp.ListItem) (enough : 2≤items.length) :
    ∃ first second,items[0]?=some first ∧ items[1]?=some second := by
  cases items with
  | nil=>simp at enough
  | cons first rest=>
    cases rest with
    | nil=>simp at enough
    | cons second rest=>exact ⟨first,second,rfl,rfl⟩

theorem DecodeSliceEntry.array_cost (input : Guest.InputBlob)
    (origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit header payload count : BitVec 64) (items : List Rlp.ListItem)
    (entry : DecodeSliceEntry input origin current db pointer length heap cursor limit header payload count items)
    (arrayCell : current.locals.lookup (ofString "arr")=some (.val (.word heap)))
    (below : cursor.toNat≤2713717616) :
    current.clock-(evaluateHOLFiniteState current Mpt.WitnessDecode.afterArray).2.clock≤payload.toNat/4+120*payload.toNat+94 := by
  let next:=PersistentAlloc.rounded heap (count*16#64)
  have rows:=entry.rows input origin current db pointer length heap cursor limit header payload count items
  have small : payload.toNat≤1024:=by have extent:=entry.extent; have bound:=entry.lengthBound; omega
  have scratchBelow : cursor.toNat≤heap.toNat:=by
    have lower:=entry.inputLower
    have before:=entry.inputBeforeHeap
    omega
  have beforeArray : heap.toNat+16*items.length≤next.toNat:=by
    have grows:=entry.snapshot.grows
    rw [entry.snapshot.countExact] at grows
    exact grows
  rw [Mpt.WitnessDecode.array_choice current heap count entry.sliceCell]
  split
  · rename_i two
    have lengthEq:=entry.snapshot.countExact
    rw [two] at lengthEq
    change 2=items.length at lengthEq
    obtain ⟨first,second,firstSelected,secondSelected⟩:=first_two items lengthEq.le
    exact Mpt.WitnessDecode.pair_cost current heap (pointer+header) next cursor limit payload.toNat items first second rows firstSelected secondSelected
      arrayCell small scratchBelow beforeArray entry.snapshot.heapCell entry.snapshot.nextArena entry.snapshot.nextAligned entry.snapshot.arena entry.installed
  · have branchPrice:=Mpt.WitnessDecode.branch_cost current next entry.snapshot.heapCell entry.snapshot.arena.domain entry.snapshot.nextArena entry.snapshot.nextAligned entry.installed
    exact branchPrice.trans (by omega)

/-- Complete unchanged original _decode_step237, with both main-constructed
databases and actual bounded input interval. All string/list decisions,
path/value parsing, compact conversion and node/record allocations are
covered, including failed reads, guards and allocations. Source call/loop
ticks are counted here; this is not yet a target-runtime certificate. -/
theorem decode_body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)).2.clock≤251*length.toNat+length.toNat/4+173 := by
  let output:=evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)
  rcases decode_array_trace input source output.2 db pointer length cursor limit boundary dbCell pointerCell lengthCell arena before small inputAbove below installed output.1 rfl with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨origin,current,header,payload,heap,count,items,inner,entry,above,globals,forward,price,continued,endpoint⟩:=reached
    have arrayCell : (bind current "arr" heap).locals.lookup (ofString "arr")=some (.val (.word heap)):=bind_lookup_same _ _ _
    have tail:=entry.array_cost input origin (bind current "arr" heap) db pointer length heap cursor limit header payload count items arrayCell below
    rw [continued] at tail
    change current.clock-inner.clock≤payload.toNat/4+120*payload.toNat+94 at tail
    have remainingForward:=evaluateHOLFiniteState_clock_le (bind current "arr" heap) Mpt.WitnessDecode.afterArray
    rw [continued] at remainingForward
    change inner.clock≤current.clock at remainingForward
    have finalClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    have extent:=entry.extent
    change source.clock-output.2.clock≤251*length.toNat+length.toNat/4+173
    rw [finalClock]
    omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.DecodeSliceEntry.array_cost
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_body_cost

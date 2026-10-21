import InitECandidate.Solver.Mpt.WitnessCoreStackView
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Transport the whole physical active stack across the actual incoming
old-storage agreement band. Allocation frontiers and record order are
retained even when the current heap grows and scratch cursor decreases. -/
theorem View.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap nextCursor nextHeap : Nat) (stack : List Entry) (view : View source db cursor heap stack)
    (heapLower : 2713731432≤heap) (drops : nextCursor≤cursor) (grows : heap≤nextHeap)
    (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,cursor≤query.toNat→ query.toNat<heap→ target.memory query=source.memory query) :
    View target db nextCursor nextHeap stack := by
  have recordBefore (entry : Entry) (member : entry∈stack) : entry.record.toNat+88≤heap:=by
    have bound:=(view.records entry member).ceiling
    omega
  have recordMemory (entry : Entry) (member : entry∈stack) : target.memory entry.record=source.memory entry.record:=
    memory entry.record (view.above entry member) (by have bound:=recordBefore entry member; omega)
  have records (entry : Entry) (member : entry∈stack) : WitnessRecord.View target entry.record db entry.data:=by
    have old:=view.records entry member
    have before:=(view.before entry member).mono entry.data entry.mark heap (view.marks entry member)
    have recordUpper:=old.ceiling
    have recordAbove:=view.above entry member
    have arrayFloor:=old.arrayFloor
    have payloadFloor:=old.payloadFloor
    exact old.interval_frame source target entry.record db entry.data cursor heap recordAbove (recordBefore entry member)
      (by omega) before.1 (by omega) before.2 domain memory
  have pending (entry : Entry) (member : entry∈stack) : Pending target db entry:=by
    have old:=view.pending entry member
    cases pendingEq : entry.pending with
    | none=>simp [Pending,pendingEq]
    | some hash=>
      simp only [Pending,pendingEq] at old ⊢
      have recordView:=view.records entry member
      have upper:=recordView.ceiling
      have above:=view.above entry member
      have number : (entry.record+80#64).toNat=entry.record.toNat+80:=byteAddress_toNat entry.record 80 (by omega)
      exact ⟨(memory (entry.record+80#64) (by omega) (by omega)).trans old.1,old.2⟩
  exact ⟨records,view.before,fun entry member=>(view.marks entry member).trans grows,
    fun entry member=>drops.trans (view.above entry member),view.links.frame source target stack recordMemory,pending,view.ordered,view.counters⟩

/-- The complete genuine decoder memory frame preserves every older
activation and its pending hash at the actual next heap/scratch cursors.
This includes the real core PREV store, which its caller frame already
places below the incoming scratch cursor. -/
theorem of_decode_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit : BitVec 64) (stack : List Entry) (view : View source db cursor.toNat heap.toNat stack)
    (heapLower : 2713731432≤heap.toNat) (frame : WitnessDecode.NormalFrame source target heap cursor limit) :
    ∃ nextHeap nextCursor,
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      Rlp.Validation.Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ heap.toNat≤nextHeap.toNat ∧
      View target db nextCursor.toNat nextHeap.toNat stack := by
  obtain ⟨nextHeap,heapCell,heapArena,aligned,grows⟩:=frame.nextHeap
  obtain ⟨nextCursor,scratch,drops⟩:=frame.nextScratch
  exact ⟨nextHeap,nextCursor,heapCell,heapArena,aligned,scratch,drops,grows,
    view.frame source target db cursor.toNat heap.toNat nextCursor.toNat nextHeap.toNat stack heapLower drops grows frame.domain frame.memory⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.of_decode_frame

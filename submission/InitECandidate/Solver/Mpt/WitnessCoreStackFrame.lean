import InitECandidate.Solver.Mpt.WitnessCoreStackView
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Persistent rows/payloads lie below the incoming heap; older scratch
records lie above the incoming cursor. Both protected sides are required
as the real heap grows and the real scratch cursor decreases. -/
theorem View.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap nextCursor nextHeap : Nat) (stack : List Entry) (view : View source db cursor heap stack)
    (drops : nextCursor≤cursor) (grows : heap≤nextHeap)
    (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,query.toNat<heap ∨ cursor≤query.toNat→target.memory query=source.memory query) :
    View target db nextCursor nextHeap stack := by
  have recordMemory (entry : Entry) (member : entry∈stack) : target.memory entry.record=source.memory entry.record:=
    memory entry.record (Or.inr (view.above entry member))
  have records (entry : Entry) (member : entry∈stack) : WitnessRecord.View target entry.record db entry.data:=by
    have before:=(view.before entry member).mono entry.data entry.mark heap (view.marks entry member)
    exact (view.records entry member).regions_frame source target entry.record db heap cursor entry.data before
      (view.above entry member) domain (fun query earlier=>memory query (Or.inl earlier)) (fun query above=>memory query (Or.inr above))
  have pending (entry : Entry) (member : entry∈stack) : Pending target db entry:=by
    have old:=view.pending entry member
    cases pendingEq : entry.pending with
    | none=>simp [Pending,pendingEq]
    | some hash=>
      simp only [Pending,pendingEq] at old ⊢
      have recordView:=view.records entry member
      have number : (entry.record+80#64).toNat=entry.record.toNat+80:=byteAddress_toNat entry.record 80 (by have upper:=recordView.arena.upper; omega)
      exact ⟨(memory (entry.record+80#64) (Or.inr (by have above:=view.above entry member; omega))).trans old.1,old.2⟩
  exact ⟨records,view.before,fun entry member=>(view.marks entry member).trans grows,
    fun entry member=>drops.trans (view.above entry member),view.links.frame source target stack recordMemory,pending,view.ordered,view.counters⟩

/-- Local bindings, clocks and lexical restorations preserve the entire
physical stack when the actual ordinary memory/domain are unchanged. -/
theorem View.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (stack : List Entry) (view : View source db cursor heap stack)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) : View target db cursor heap stack := by
  have records (entry : Entry) (member : entry∈stack) : WitnessRecord.View target entry.record db entry.data:=
    (view.records entry member).of_fields source target entry.record db entry.data memory domain
  have pending (entry : Entry) (member : entry∈stack) : Pending target db entry:=by
    have old:=view.pending entry member
    cases observed : entry.pending <;> simpa only [Pending,observed,memory] using old
  exact ⟨records,view.before,view.marks,view.above,
    view.links.frame source target stack (fun entry member=>congrFun memory entry.record),pending,view.ordered,view.counters⟩

/-- The complete genuine decoder memory frame preserves every older
activation and its pending hash at the actual next heap/scratch cursors.
This includes the real core PREV store, which its caller frame already
places below the incoming scratch cursor. -/
theorem of_decode_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit : BitVec 64) (stack : List Entry) (view : View source db cursor.toNat heap.toNat stack)
    (frame : WitnessDecode.LiveFrame source target heap cursor limit) :
    ∃ nextHeap nextCursor,
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      Rlp.Validation.Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ heap.toNat≤nextHeap.toNat ∧
      View target db nextCursor.toNat nextHeap.toNat stack := by
  obtain ⟨nextHeap,heapCell,heapArena,bounded,aligned,grows⟩:=frame.nextHeap
  obtain ⟨nextCursor,scratch,drops⟩:=frame.nextScratch
  exact ⟨nextHeap,nextCursor,heapCell,heapArena,aligned,scratch,drops,grows,
    view.frame source target db cursor.toNat heap.toNat nextCursor.toNat nextHeap.toNat stack drops grows frame.domain frame.memory⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.of_decode_frame

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.of_fields

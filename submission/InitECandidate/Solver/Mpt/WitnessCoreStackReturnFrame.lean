import InitECandidate.Solver.Mpt.WitnessCoreStackFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

def resultLower : List Entry→Nat | []=>2713731432 | entry::_=>entry.mark

theorem View.result_lower_le_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (stack : List Entry) (view : View source db cursor heap stack) (heapLower : 2713731432≤heap) :
    resultLower stack≤heap := by
  cases stack with
  | nil=>exact heapLower
  | cons entry rest=>exact view.marks entry List.mem_cons_self

theorem View.parent_result_lower (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest)) :
    resultLower rest≤entry.data.payload.startAddress := by
  cases rest with
  | nil=>exact (view.records entry List.mem_cons_self).payloadFloor
  | cons parent older=>exact (view.ordered.1 parent List.mem_cons_self).2.2

/-- The older stack occupies the band above the current head record and
below its fresh stage payload. Return-mode child/counter/value/metadata
stores lie outside that band; the real item parser preserves it as well.
This frames the entire older PREV/HASH chain at the actual next cursors. -/
theorem View.return_tail_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap nextCursor nextHeap : Nat) (entry : Entry) (rest : List Entry)
    (view : View source db cursor heap (entry::rest)) (drops : nextCursor≤cursor) (grows : heap≤nextHeap)
    (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,entry.record.toNat+88≤query.toNat→ query.toNat<entry.data.payload.startAddress→
      target.memory query=source.memory query) : View target db nextCursor nextHeap rest := by
  have tail:=view.tail_after_record source db cursor heap entry rest
  have old : View source db (entry.record.toNat+88) entry.data.payload.startAddress rest:=
    ⟨tail.records,tail.before,fun parent member=>(view.ordered.1 parent member).2.2,
      tail.above,tail.links,tail.pending,tail.ordered,tail.counters⟩
  have recordView:=view.records entry List.mem_cons_self
  have before:=view.before entry List.mem_cons_self
  have mark:=view.marks entry List.mem_cons_self
  have recordAbove:=view.above entry List.mem_cons_self
  have startEnd : entry.data.payload.startAddress≤entry.data.payload.endAddress:=by
    cases payloadEq : entry.data.payload with
    | extension nibbles length=>simp only [payloadEq,WitnessRecord.Payload.startAddress,WitnessRecord.Payload.endAddress]; omega
    | branch node index occupied=>simp only [payloadEq,WitnessRecord.Payload.startAddress,WitnessRecord.Payload.endAddress]; omega
  exact old.frame source target db (entry.record.toNat+88) entry.data.payload.startAddress nextCursor nextHeap rest
    recordView.payloadFloor (by omega) (by have bound:=before.2; omega) domain memory

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.return_tail_frame

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.result_lower_le_heap
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.parent_result_lower

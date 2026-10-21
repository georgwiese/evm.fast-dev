import InitECandidate.Solver.Mpt.WitnessCoreStackFrame
import InitECandidate.Solver.Mpt.WitnessCoreResolveState

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Install the actual resolver's new pending hash in the current head.
The real ordered record addresses preserve every older PREV/HASH cell;
persistent rows/stage payloads lie above the whole scratch record band. -/
theorem set_pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db hash : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest))
    (heapLower : 2713731432≤heap) (valid : HashValid db hash) :
    View (hashState source entry.record hash) db cursor heap ({entry with pending:=some hash}::rest) := by
  let target:=hashState source entry.record hash
  have recordView:=view.records entry List.mem_cons_self
  have recordUpper:=recordView.ceiling
  have number : (entry.record+80#64).toNat=entry.record.toNat+80:=byteAddress_toNat entry.record 80 (by omega)
  have tail:=view.tail_after_record source db cursor heap entry rest
  have framedTail : View target db (entry.record.toNat+88) heap rest:=by
    apply tail.frame source target db (entry.record.toNat+88) heap (entry.record.toNat+88) heap rest heapLower (Nat.le_refl _) (Nat.le_refl _) rfl
    intro query lower upper
    have away : query≠entry.record+80#64:=by intro same; have numeric:=congrArg BitVec.toNat same; rw [number] at numeric; omega
    exact if_neg away
  have headAbove:=view.above entry List.mem_cons_self
  have oldTail:=framedTail.lower_cursor target db (entry.record.toNat+88) cursor heap rest (by omega)
  have headView:=recordView.hashed source entry.record db hash entry.data
  have link : target.memory entry.record=.word (top rest):=
    (recordView.hash_preserves_previous source entry.record db hash entry.data).trans view.links.1
  have pending : Pending target db {entry with pending:=some hash}:=by
    exact ⟨by simp [target,hashState,StoreWord.put],valid⟩
  exact View.cons target db cursor heap {entry with pending:=some hash} rest oldTail headView
    (view.before entry List.mem_cons_self) (view.marks entry List.mem_cons_self) headAbove link pending view.ordered.1
    (view.counters entry List.mem_cons_self)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.set_pending

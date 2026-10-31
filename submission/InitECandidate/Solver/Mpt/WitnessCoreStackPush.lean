import InitECandidate.Solver.Mpt.WitnessCoreStackFrame
import InitECandidate.Solver.Mpt.WitnessDecodeResult
import InitECandidate.Solver.Mpt.WitnessRecordRank

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem fresh_counters (data : WitnessRecord.Description) (fresh : data.payload.Fresh) : CounterBound data := by
  cases payloadEq : data.payload with
  | extension nibbles length=>simp [CounterBound,payloadEq]
  | branch node index occupied=>
    simp only [WitnessRecord.Payload.Fresh,payloadEq] at fresh
    simp only [CounterBound,payloadEq]
    omega

/-- Install a physically initialized fresh record at the head of the
actual PREV chain, retaining every older ownership/frontier invariant. -/
theorem push (post : PanSemStateFiniteExact 64 Guest.HostMemory) (db record : BitVec 64)
    (cursor heap : Nat) (data : WitnessRecord.Description) (rest : List Entry)
    (old : View post db cursor heap rest) (view : WitnessRecord.View post record db data)
    (before : data.BeforeHeap heap) (above : cursor≤record.toNat) (fresh : data.payload.Fresh)
    (order : ∀ parent∈rest,record.toNat+88≤parent.record.toNat ∧ parent.mark≤data.array.toNat ∧ parent.mark≤data.payload.startAddress)
    (link : post.memory record=.word (top rest)) :
    View post db cursor heap ({record:=record,data:=data,mark:=heap,pending:=none}::rest) := by
  exact View.cons post db cursor heap ⟨record,data,heap,none⟩ rest old view before (Nat.le_refl _) above link True.intro order
    (fresh_counters data fresh)

/-- The complete genuine decoder's record result and actual core PREV
store supply a physical push and strict rank decrease. All fresh extents,
the new allocation frontier and scratch room are derived from that same
returned result; older active frames come from its actual memory frame. -/
theorem push_record_result (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (stack : List Entry)
    (old : View source db cursor.toNat heap.toNat stack)
    (arena : Rlp.Validation.Arena source cursor limit)
    (frame : WitnessDecode.LiveFrame source post heap cursor limit)
    (result : WitnessDecode.NormalResult post db pointer length heap cursor limit
      (.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))]))
    (link : post.memory (WitnessRecord.pointer cursor)=.word (top stack)) :
    ∃ data : WitnessRecord.Description, ∃ next,
      let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
      View post db (WitnessRecord.pointer cursor).toNat next.toNat (entry::stack) ∧ data.payload.Fresh ∧ data.payload.InitialValue post ∧
      data.pointer=pointer ∧ data.length=length ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
      AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit ∧
      heap.toNat≤next.toNat ∧
      heap.toNat≤data.array.toNat ∧ heap.toNat≤data.payload.startAddress ∧
      WitnessStackRank.rank (WitnessStackRank.recordsLeft (WitnessRecord.pointer cursor).toNat limit.toNat) (frames (entry::stack)) .resolve true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames stack) .decode true := by
  cases result with
  | record data next view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop=>
    have room : Arenas.Room .down cursor limit 88#64:=by
      change limit.toNat+88≤cursor.toNat
      omega
    have bounds:=WitnessRecord.allocation_bounds source cursor limit arena room
    have recordUpper : (WitnessRecord.pointer cursor).toNat+88≤cursor.toNat:=bounds.2.2.1
    obtain ⟨actualHeap,actualCell,actualArena,actualBound,actualAligned,grows⟩:=frame.nextHeap
    have same : actualHeap=next:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst actualHeap
    have oldPost:=old.frame source post db cursor.toNat heap.toNat (WitnessRecord.pointer cursor).toNat next.toNat stack
      (by omega) grows frame.domain frame.memory
    have order (parent : Entry) (member : parent∈stack) :
        (WitnessRecord.pointer cursor).toNat+88≤parent.record.toNat ∧ parent.mark≤data.array.toNat ∧ parent.mark≤data.payload.startAddress:=by
      have parentAbove:=old.above parent member
      have mark:=old.marks parent member
      exact ⟨by omega,mark.trans freshRows,mark.trans freshPayload⟩
    have pushed:=push post db (WitnessRecord.pointer cursor) (WitnessRecord.pointer cursor).toNat next.toNat data stack oldPost view before
      (Nat.le_refl _) fresh order link
    exact ⟨data,next,pushed,fresh,initial,parentPointer,parentLength,heapCell,heapArena,heapAligned,scratch,grows,freshRows,freshPayload,
      WitnessRecord.allocation_rank_push source cursor limit arena room (frames stack) data.payload⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.fresh_counters
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.push
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.push_record_result

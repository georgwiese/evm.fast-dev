import InitECandidate.Solver.Headers.DecodeSliceState
import InitECandidate.Solver.Headers.FieldState

namespace InitECandidate.Solver.Headers.Decode
open Flapjack PanSemStateFiniteExact
open WitnessRadix

/-- The true original parsed/count-checked/allocation prefix supplies the
initial full field-pipeline state. No local slot, completed header image or
future field execution is assumed; active slots start empty. -/
theorem initial_field_state (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem) (cutoff : Nat)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items)
    (countValid : count=21#64 ∨ count=23#64)
    (headerRoom : (PersistentAlloc.rounded heap (count*16#64)).toNat+248≤33806089496)
    (installed : Input.OriginalCode.Installed source.code)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (cutoffAligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat) :
    FieldState (fieldEntry source parsed sliced pointer header payload heap count) (pointer+header) heap
      (PersistentAlloc.rounded heap (count*16#64)) cursor limit (if count=23#64 then 1#64 else 0#64) payload.toNat cutoff items [] := by
  let listSource:=listState source parsed sliced pointer header payload heap count
  let current:=counted (declared listSource heap count) count
  let target:=fieldEntry source parsed sliced pointer header payload heap count
  let outputPointer:=PersistentAlloc.rounded heap (count*16#64)
  have heapLower : 2701131776≤heap.toNat := by omega
  have extent := (Rlp.Decode.Complete.fields pointer length header payload 1#64 topReturned.complete).2.2.1
  have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by have h:=heap.isLt; omega)
  have product : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by have h:=slicesReturned.room; change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have allocationRoom : heap.toNat+(count*16#64).toNat≤33806089496 := by rw [product]; exact slicesReturned.room
  have guards:=PersistentAlloc.guards heap (count*16#64) allocationRoom
  have context:=(counted_frame listSource heap count).1
  have code:=congrArg PanSemStateFiniteExact.code context
  change target.code=sliced.code at code
  have originalCode : target.code=source.code := code.trans (slicesReturned.code.trans topReturned.code)
  obtain ⟨headerCell,arrayCell,countCell,currentCell,heapCell,_,_⟩ := allocation_fields listSource heap count outputPointer
  refine ⟨field_entry_state source parsed sliced pointer length header payload heap cursor limit count items cutoff topReturned slicesReturned heapLower heapAligned before cutoffAligned scratchBelow inputAbove,
    Slots.empty target,by rw [originalCode]; exact installed,arrayCell,headerCell,currentCell,?_,?_,?_,guards.2.2.2.2,?_,heapCell⟩
  · by_cases current : count=23#64
    · refine Or.inr ⟨by simp [current],?_⟩
      rw [←slicesReturned.countEq,current]
      rfl
    · have parent : count=21#64 := countValid.resolve_right current
      refine Or.inl ⟨by simp [current],?_⟩
      rw [←slicesReturned.countEq,parent]
      rfl
  · refine ⟨by rw [pointerNumber]; omega,?_⟩
    rw [pointerNumber]
    have h:=slicesReturned.room
    omega
  · refine ⟨?_,headerRoom⟩
    have lower:=guards.2.2.1
    change heap.toNat+(count*16#64).toNat≤outputPointer.toNat at lower
    omega
  · rw [←slicesReturned.countEq]
    have lower:=guards.2.2.1
    rw [product] at lower
    exact lower

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.initial_field_state

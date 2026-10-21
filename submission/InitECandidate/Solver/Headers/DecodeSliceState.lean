import InitECandidate.Solver.Headers.DecodeEntryTrace
import InitECandidate.Solver.Headers.SliceState
import InitECandidate.Solver.Rlp.DecodeFields

namespace InitECandidate.Solver.Headers.Decode
open Flapjack PanSemStateFiniteExact
open WitnessRadix

/-- Derive the actual current slice-state invariant at the original header
field entry from the two real parser returns and original allocation. The
record count and every input byte/array fact refer to this reached state. -/
theorem field_entry_state (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem) (cutoff : Nat)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items)
    (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (cutoffAligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat) :
    SliceState (fieldEntry source parsed sliced pointer header payload heap count) (pointer+header) heap cursor limit payload.toNat cutoff items := by
  let listSource:=listState source parsed sliced pointer header payload heap count
  let current:=counted (declared listSource heap count) count
  let target:=fieldEntry source parsed sliced pointer header payload heap count
  let outputPointer:=PersistentAlloc.rounded heap (count*16#64)
  have extent := (Rlp.Decode.Complete.fields pointer length header payload 1#64 topReturned.complete).2.2.1
  have heapFits:=heap.isLt
  have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have allocation : AllocatedBytes.Arena heap (16*items.length) :=
    ⟨heapLower,by rw [←slicesReturned.countEq]; exact slicesReturned.room⟩
  have initial : SliceState sliced (pointer+header) heap cursor limit payload.toNat cutoff items :=
    ⟨slicesReturned.itemsAtReturn,slicesReturned.records,slicesReturned.arena,allocation,heapAligned,
      by rw [pointerNumber]; omega,by rw [pointerNumber]; omega,cutoffAligned,scratchBelow,
      by rw [pointerNumber]; omega,by omega⟩
  have context := (counted_frame listSource heap count).1
  have domain:=congrArg PanSemStateFiniteExact.memaddrs context
  have endian:=congrArg PanSemStateFiniteExact.be context
  have globals:=congrArg PanSemStateFiniteExact.globals context
  change current.memaddrs=sliced.memaddrs at domain
  change current.be=sliced.be at endian
  change current.globals=sliced.globals at globals
  have currentArena:=Rlp.Validation.Arena.of_fields sliced current cursor limit slicesReturned.arena domain globals
  have targetArena : Rlp.Validation.Arena target cursor limit :=
    Rlp.Validation.Arena.heap_updated current target cursor limit (PersistentAlloc.rounded outputPointer 248#64) currentArena rfl rfl
  obtain ⟨_,_,_,_,_,memory,_⟩ := allocation_fields listSource heap count outputPointer
  change target.memory=sliced.memory at memory
  apply initial.of_parts sliced target (pointer+header) heap cursor limit payload.toNat cutoff items targetArena
  · rw [memory]
    exact slicesReturned.records
  · intro offset inside
    unfold Rlp.ReadLength.byte
    exact MemoryBytes.read_of_fields sliced target memory.symm domain.symm endian.symm _

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.field_entry_state

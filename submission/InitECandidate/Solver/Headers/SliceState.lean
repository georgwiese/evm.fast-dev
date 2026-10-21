import InitECandidate.Solver.Headers.FieldRows
import InitECandidate.Solver.Rlp.ByteAgreementFrame
import InitECandidate.Solver.Rlp.SlicesNormalFrames
import InitECandidate.Solver.Rlp.SliceRecordsFrame

namespace InitECandidate.Solver.Headers
open Flapjack PanSemStateFiniteExact
open WitnessRadix

/-- Current physical RLP input and record-array evidence used by the
unchanged header fields. No future helper result or memory model is stored. -/
structure SliceState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array cursor limit : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) : Prop where
  itemsAtInput : Rlp.ListItems source pointer bytes items
  records : Rlp.Slices.Records source.memory array pointer items
  arena : Rlp.Validation.Arena source cursor limit
  arrayArena : AllocatedBytes.Arena array (16*items.length)
  arrayAligned : array.toNat%8=0
  inputFits : pointer.toNat+bytes<2^64
  inputBefore : pointer.toNat+bytes≤array.toNat
  cutoffAligned : cutoff%8=0
  scratchBelow : cursor.toNat≤cutoff
  inputAbove : cutoff≤pointer.toNat
  arrayAbove : cutoff≤array.toNat

theorem SliceState.of_parts (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array cursor limit : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items)
    (arena : Rlp.Validation.Arena target cursor limit)
    (records : Rlp.Slices.Records target.memory array pointer items)
    (bytesAgree : ∀ offset : BitVec 64,offset.toNat<bytes → Rlp.ReadLength.byte source (pointer+offset)=Rlp.ReadLength.byte target (pointer+offset)) :
    SliceState target pointer array cursor limit bytes cutoff items :=
  ⟨state.itemsAtInput.transport source target pointer bytes items (by have h:=state.inputFits; omega) bytesAgree,
    records,arena,state.arrayArena,state.arrayAligned,state.inputFits,state.inputBefore,state.cutoffAligned,state.scratchBelow,state.inputAbove,state.arrayAbove⟩

/-- Normal original field-helper scratch footprints preserve the current
ordered input encodings and the actual independent record array together. -/
theorem SliceState.above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array cursor limit : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items)
    (arena : Rlp.Validation.Arena target cursor limit) (frame : Rlp.Validation.Above source target cursor.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) : SliceState target pointer array cursor limit bytes cutoff items := by
  have small : bytes<2^64 := by have h:=state.inputFits; omega
  have size : (BitVec.ofNat 64 bytes).toNat=bytes := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have byteFrame:=Rlp.Validation.Above.bytes_agree source target cutoff pointer (BitVec.ofNat 64 bytes)
    (Rlp.Validation.Above.mono source target cursor.toNat cutoff frame state.scratchBelow) state.cutoffAligned state.inputAbove
    (by rw [size]; exact state.inputFits) domain endian
  apply state.of_parts source target pointer array cursor limit bytes cutoff items arena
  · exact Rlp.Slices.Records.above source target array pointer items cursor.toNat state.records frame
      (state.scratchBelow.trans state.arrayAbove) (by have h:=state.arrayArena.upper; omega)
  · intro offset inside
    exact byteFrame offset (by rw [size]; exact inside)

/-- An actual output-header word store after the slice allocation preserves
all current source encodings and record cells. This also covers the stores
of individual words within the four-word integer fields. -/
theorem SliceState.store_after (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array cursor limit address value : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items)
    (afterArray : array.toNat+16*items.length≤address.toNat) :
    SliceState {source with memory:=StoreWord.put source.memory address value} pointer array cursor limit bytes cutoff items := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory address value}
  have frame : Rlp.Slices.Window source target address.toNat (address.toNat+1) := by
    intro query outside
    change StoreWord.put source.memory address value query=source.memory query
    apply if_neg
    intro same
    have equal:=congrArg BitVec.toNat same
    rcases outside with before|after <;> omega
  have small : bytes<2^64 := by have h:=state.inputFits; omega
  have size : (BitVec.ofNat 64 bytes).toNat=bytes := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have byteFrame:=frame.bytes_before source target address.toNat (address.toNat+1) pointer (BitVec.ofNat 64 bytes)
    (by rw [size]; have h:=state.inputBefore; omega) (by rw [size]; exact state.inputFits) rfl rfl
  apply state.of_parts source target pointer array cursor limit bytes cutoff items
    (Rlp.Validation.Arena.of_fields source target cursor limit state.arena rfl rfl)
  · apply Rlp.Slices.Records.of_interval source target array pointer items state.records (by have h:=state.arrayArena.upper; omega)
    intro query lower upper
    exact frame query (Or.inl (by omega))
  · intro offset inside
    exact byteFrame offset (by rw [size]; exact inside)

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.SliceState.of_parts
#print axioms InitECandidate.Solver.Headers.SliceState.above
#print axioms InitECandidate.Solver.Headers.SliceState.store_after

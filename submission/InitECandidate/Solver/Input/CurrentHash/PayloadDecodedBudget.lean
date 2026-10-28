import InitECandidate.Solver.Input.PayloadReturnedImage
import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionEntry

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual validated payload offsets, interpreted without word wrapping. -/
theorem offset_ranges {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array : BitVec 64} {length start size : Nat}
    (data : Payload.ReturnedImage input source blob record array length start size) (inputBound : input.length%2^64≤251655056) :
    62+length≤input.length%2^64 ∧ (BitVec.ofNat 64 length).toNat=length ∧
    (∀ index<4,540≤(Payload.offsetWords input index).toNat ∧ (Payload.offsetWords input index).toNat≤length) ∧
    (Payload.offsetWords input 2).toNat≤(Payload.offsetWords input 3).toNat := by
  have upper := data.sliceUpper
  have minimum := data.minimum
  have number : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega,number,?_,?_⟩
  · intro index inside
    have valid:=data.valid index inside
    change 540≤(Payload.offsetWords input index).toNat ∧ (Payload.offsetWords input index).toNat≤_ ∧ _ at valid
    rw [number] at valid
    exact ⟨valid.1,valid.2.1⟩
  · exact (data.valid 3 (by decide)).2.2 (by decide)

/-- Any real payload byte subrange is inside the same copied input arena. -/
theorem payload_slice_arena (blob : BitVec 64) (inputLength length : Nat) (offset : BitVec 64) (n : Nat)
    (inputArena : AllocatedBytes.Arena blob inputLength) (sliceUpper : 62+length≤inputLength) (inside : offset.toNat+n≤length) :
    AllocatedBytes.Arena (blob+62#64+offset) n := by
  have arena := AllocatedBytes.Arena.subrange blob inputLength (62+offset.toNat) n inputArena (by omega)
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using arena

theorem raw_arena {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array : BitVec 64} {length start size : Nat}
    (data : Payload.ReturnedImage input source blob record array length start size) (inputBound : input.length%2^64≤251655056)
    (inputArena : AllocatedBytes.Arena blob (input.length%2^64)) : AllocatedBytes.Arena (blob+62#64) 540 := by
  have upper := (offset_ranges data inputBound).1
  have minimum := data.minimum
  exact AllocatedBytes.Arena.subrange blob (input.length%2^64) 62 540 inputArena (by omega)

/-- The genuine returned withdrawal and balance cells supply their exact
count/length, complete physical input extents and bounded hash arguments.
No schema maximum such as sixteen withdrawals is assumed. -/
theorem remaining_regions {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array : BitVec 64} {length start size : Nat}
    (data : Payload.ReturnedImage input source blob record array length start size) (inputBound : input.length%2^64≤251655056)
    (inputArena : AllocatedBytes.Arena blob (input.length%2^64)) :
    ∃ count : BitVec 64,
      source.memory (record+48#64)=.word (blob+62#64+Payload.offsetWords input 2) ∧ source.memory (record+56#64)=.word count ∧
      source.memory (record+64#64)=.word (blob+62#64+Payload.offsetWords input 3) ∧
      source.memory (record+72#64)=.word (BitVec.ofNat 64 length-Payload.offsetWords input 3) ∧
      count.toNat≤134217728 ∧ 44*count.toNat=(Payload.offsetWords input 3).toNat-(Payload.offsetWords input 2).toNat ∧
      AllocatedBytes.Arena (blob+62#64+Payload.offsetWords input 2) (44*count.toNat) ∧
      (BitVec.ofNat 64 length-Payload.offsetWords input 3).toNat=length-(Payload.offsetWords input 3).toNat ∧
      (BitVec.ofNat 64 length-Payload.offsetWords input 3).toNat≤251655056 ∧
      AllocatedBytes.Arena (blob+62#64+Payload.offsetWords input 3) (BitVec.ofNat 64 length-Payload.offsetWords input 3).toNat := by
  obtain ⟨count,cells,division,remainder⟩ := data.remaining
  have ranges := offset_ranges data inputBound
  have second := ranges.2.2.1 2 (by decide)
  have third := ranges.2.2.1 3 (by decide)
  have ordered := ranges.2.2.2
  have difference : (Payload.offsetWords input 3-Payload.offsetWords input 2).toNat=(Payload.offsetWords input 3).toNat-(Payload.offsetWords input 2).toNat :=
    BitVec.toNat_sub_of_le (show Payload.offsetWords input 2≤Payload.offsetWords input 3 from ordered)
  rw [difference] at division remainder
  have exactBytes : 44*count.toNat=(Payload.offsetWords input 3).toNat-(Payload.offsetWords input 2).toNat := by omega
  have balance : (BitVec.ofNat 64 length-Payload.offsetWords input 3).toNat=length-(Payload.offsetWords input 3).toNat := by
    rw [BitVec.toNat_sub_of_le (show Payload.offsetWords input 3≤BitVec.ofNat 64 length from by change (Payload.offsetWords input 3).toNat≤(BitVec.ofNat 64 length).toNat; rw [ranges.2.1]; exact third.2),ranges.2.1]
  have fields := cells.hash_fields
  refine ⟨count,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,by omega,exactBytes,?_,balance,by omega,?_⟩
  · exact payload_slice_arena blob (input.length%2^64) length (Payload.offsetWords input 2) (44*count.toNat) inputArena ranges.1 (by omega)
  · exact payload_slice_arena blob (input.length%2^64) length (Payload.offsetWords input 3) _ inputArena ranges.1 (by omega)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.offset_ranges
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.payload_slice_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.raw_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.remaining_regions

import InitECandidate.Solver.Input.CopyMemory
import InitECandidate.Solver.Input.ByteDecode
import InitECandidate.Solver.Input.CopyDomain

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact

theorem dataBytes_at (input : Guest.InputBlob) (start index : Nat) (inside : index<8) :
    ((HostWords.dataBytes input start)[index]?).getD 0=Framing.convert ((input[start+index]?).getD 0) := by
  rw [List.getElem?_eq_getElem (by simpa [HostWords.dataBytes] using inside)]
  simp [HostWords.dataBytes]

/-- Bytes read from the copied heap agree with the challenge's input bytes,
including padding beyond the actual list end; no bound on the mathematical list is used. -/
theorem walk_byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (length offset : Nat) (bounded : length≤Guest.maxInputBytes)
    (inside : offset<8*copyRounds length)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+length+8≤33806089496)
    (aligned : pointer.toNat%8=0) (little : source.be=false)
    (domain : source.memaddrs=InitE.ordinaryDomain) (host : source.ffi.ffiState=Guest.guestHostMemory input) :
    @panMemLoadByteHOL 64 _ (walk source pointer 0 (copyRounds length)).memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 offset)=some (Framing.convert ((input[offset]?).getD 0)) := by
  have fit:=copyRounds_fit length bounded
  have wordInside : offset/8<copyRounds length := by omega
  have startInside : 8*(offset/8)<length := by
    dsimp [copyRounds] at wordInside
    omega
  have startAligned : (8*(offset/8))%8=0 := by omega
  have visible:=HostWords.final_word_visible length (8*(offset/8)) bounded startInside startAligned
  have cell:=walk_cell source pointer 0 (copyRounds length) (offset/8) wordInside (by omega)
  simp only [Nat.zero_add] at cell
  rw [host,HostWords.bytes input _ visible] at cell
  have addressNat:=WitnessRadix.MemoryBytes.offset_toNat pointer offset (by omega)
  have wordNat:=WitnessRadix.MemoryBytes.offset_toNat pointer (8*(offset/8)) (by omega)
  have alignment : panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset)=pointer+BitVec.ofNat 64 (8*(offset/8)) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 (((pointer+BitVec.ofNat 64 offset).toNat/8)*8)).toNat=_
    rw [BitVec.toNat_ofNat,addressNat,wordNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have mapped : source.memaddrs (pointer+BitVec.ofNat 64 (8*(offset/8))) := by
    rw [domain]
    exact heap_copy_mapped pointer length _ lower upper aligned startInside startAligned
  have digit : (pointer+BitVec.ofNat 64 offset).toNat%8=offset%8 := by rw [addressNat]; omega
  have decode:=WordCodec.decoded_byte (HostWords.dataBytes input (8*(offset/8)))
    (HostWords.dataBytes_length _ _) (offset%8) (by omega)
  have modByte (number : Nat) : UInt8.ofNat (number%256)=UInt8.ofNat number := by
    apply UInt8.toNat.inj
    simp [UInt8.toNat_ofNat']
  simp only [panMemLoadByteHOL,alignment,mapped,↓reduceIte,cell,little,panGetByteHOL]
  change some (UInt8.ofNat (((Guest.wordOfLeBytes (HostWords.dataBytes input (8*(offset/8)))).toNat /
    256^((pointer+BitVec.ofNat 64 offset).toNat%8))%256))=_
  rw [digit,modByte,decode,dataBytes_at input _ _ (by omega)]
  congr 4
  omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.dataBytes_at
#print axioms InitECandidate.Solver.Input.Blob.walk_byte

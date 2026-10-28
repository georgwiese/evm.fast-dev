import InitECandidate.Solver.Input.VarList.RecordSizes

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

def recordPointer (input : Guest.InputBlob) (pointer : BitVec 64) (start index : Nat) : BitVec 64 :=
  pointer+BitVec.ofNat 64 start+currentWord input start index
def recordFirstByte (input : Guest.InputBlob) (start index : Nat) : UInt8 :=
  Framing.convert ((input[start+(currentWord input start index).toNat]?).getD 0)

/-- Real pointer cells and conditional first-byte reads. An empty item needs no
byte read at its end pointer; an empty list needs no readable record cells. -/
theorem Records.pointer_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : Blob.HeapInput source input pointer) (records : Records source input pointer array start length) :
    ∀ index<decodedCount input start length,
      source.memaddrs (row (decodedArray array length) index) ∧
      source.memory (row (decodedArray array length) index)=.word (recordPointer input pointer start index) ∧
      (recordLength input start length (decodedCount input start length) index≠0#64→
        @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
          (recordPointer input pointer start index)=some (recordFirstByte input start index)) := by
  classical
  rcases records with empty|nonempty
  · simp [decodedCount,empty]
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have slice : start+length≤input.length%2^64 := by simpa only [startEq,lengthEq] using plan.slice
    have lengthBound : length<2^64 := by have m:=Nat.mod_lt input.length (by decide : 0<2^64); omega
    have lengthWord : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthBound]
    have nonemptyLength : length≠0 := by have h:=plan.header; have p:=plan.positive; rw [lengthEq] at h; omega
    simp only [decodedCount,decodedArray,if_neg nonemptyLength]
    intro index inside
    have planInside : index<plan.count := by rw [countEq]; exact inside
    have mapped:=plan.row_mapped source domain index planInside
    have cell:=(complete index planInside).1
    refine ⟨by simpa only [arrayEq] using mapped,by simpa only [recordPointer,pointerEq,arrayEq,startEq] using cell,?_⟩
    intro nonzero
    have this:=valid index planInside
    have currentUpper : (currentWord input start index).toNat≤length := by simpa only [lengthWord] using this.2.1
    have currentInside : (currentWord input start index).toNat<length := by
      by_contra outside
      have atEnd : (currentWord input start index).toNat=length := by omega
      by_cases next : index+1<Guest.GasLimit.le32 input start/4
      · have later:=valid (index+1) (by rw [countEq]; exact next)
        have upper : (currentWord input start (index+1)).toNat≤length := by simpa only [lengthWord] using later.2.1
        have ordered:=later.2.2 (by omega)
        simp only [Nat.add_sub_cancel] at ordered
        have equal : currentWord input start (index+1)=currentWord input start index := BitVec.eq_of_toNat_eq (by omega)
        simp [recordLength,next,equal] at nonzero
      · have equal : BitVec.ofNat 64 length=currentWord input start index := BitVec.eq_of_toNat_eq (by omega)
        simp [recordLength,next,equal] at nonzero
    have address : recordPointer input pointer start index=pointer+BitVec.ofNat 64 (start+(currentWord input start index).toNat) := by
      rw [recordPointer,BitVec.ofNat_add,BitVec.ofNat_toNat,←BitVec.add_assoc]
      simp
    rw [address]
    exact heap _ (by omega)


end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.pointer_reads

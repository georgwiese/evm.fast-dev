import InitECandidate.Solver.Input.VarList.RecordPointers
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact
open WitnessRadix WitnessRadix.AllocatedBytes

/-- Every real decoded item is a non-wrapping subrange of the encoded input,
including zero-length items at its end. This bounds encoded bytes, not the
mathematical input list length. -/
theorem Records.slice_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length) :
    ∀ index<decodedCount input start length,
      (recordPointer input pointer start index).toNat=pointer.toNat+start+(currentWord input start index).toNat ∧
      (currentWord input start index).toNat+
        (recordLength input start length (decodedCount input start length) index).toNat≤length ∧
      Arena (recordPointer input pointer start index)
        (recordLength input start length (decodedCount input start length) index).toNat ∧
      (recordPointer input pointer start index).toNat+
        (recordLength input start length (decodedCount input start length) index).toNat+8≤array.toNat := by
  classical
  rcases records with empty|nonempty
  · simp [decodedCount,empty]
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have slice : start+length≤input.length%2^64 := by simpa only [startEq,lengthEq] using plan.slice
    have after : pointer.toNat+input.length%2^64+8≤array.toNat := by simpa only [pointerEq,arrayEq] using plan.arrayAfter
    have room : array.toNat≤33806089496 := by have h:=plan.arrayRoom;rw [arrayEq] at h;omega
    have lower : 2701131776≤pointer.toNat := by simpa only [pointerEq] using plan.inputLower
    have lengthBound : length<2^64 := by have m:=Nat.mod_lt input.length (by decide : 0<2^64);omega
    have lengthWord : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthBound]
    have nonemptyLength : length≠0 := by have h:=plan.header;have p:=plan.positive;rw [lengthEq] at h;omega
    simp only [decodedCount,if_neg nonemptyLength]
    intro index inside
    have planInside : index<plan.count := by rw [countEq];exact inside
    have this:=valid index planInside
    have currentUpper : (currentWord input start index).toNat≤length := by simpa only [lengthWord] using this.2.1
    have endBound : (currentWord input start index).toNat+
        (recordLength input start length (Guest.GasLimit.le32 input start/4) index).toNat≤length := by
      by_cases next : index+1<Guest.GasLimit.le32 input start/4
      · have later:=valid (index+1) (by rw [countEq];exact next)
        have upper : (currentWord input start (index+1)).toNat≤length := by simpa only [lengthWord] using later.2.1
        have ordered:=later.2.2 (by omega)
        simp only [Nat.add_sub_cancel] at ordered
        simp only [recordLength,if_pos next,BitVec.toNat_sub_of_le (show currentWord input start index≤currentWord input start (index+1) from ordered)]
        omega
      · have wordOrder : currentWord input start index≤BitVec.ofNat 64 length := by
          change (currentWord input start index).toNat≤(BitVec.ofNat 64 length).toNat
          rw [lengthWord];exact currentUpper
        simp only [recordLength,if_neg next,BitVec.toNat_sub_of_le wordOrder,lengthWord]
        omega
    have startWord : (BitVec.ofNat 64 start).toNat=start := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have address : (recordPointer input pointer start index).toNat=pointer.toNat+start+(currentWord input start index).toNat := by
      rw [recordPointer,BitVec.toNat_add_of_lt (by
        rw [BitVec.toNat_add_of_lt (by rw [startWord];omega),startWord];omega),
        BitVec.toNat_add_of_lt (by rw [startWord];omega),startWord]
    refine ⟨address,endBound,⟨?_,?_⟩,?_⟩
    · rw [address];omega
    · rw [address];omega
    · rw [address];omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.slice_geometry

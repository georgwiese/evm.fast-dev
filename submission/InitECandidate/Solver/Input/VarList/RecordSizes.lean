import InitECandidate.Solver.Input.VarList.RecordCells

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

def sumPrefix (size : Nat→Nat) : Nat→Nat
  | 0=>0
  | index+1=>sumPrefix size index+size index
def recordOffset (input : Guest.InputBlob) (start length count index : Nat) : Nat :=
  if index<count then (currentWord input start index).toNat else length

theorem prefix_telescope (offset size : Nat→Nat) (count : Nat)
    (ordered : ∀ index<count,offset index≤offset (index+1))
    (difference : ∀ index<count,size index=offset (index+1)-offset index) :
    ∀ index≤count,sumPrefix size index+offset 0=offset index := by
  intro index inside
  induction index with
  | zero=>simp [sumPrefix]
  | succ index ih=>
    have prev:=ih (by omega)
    have increasing:=ordered index (by omega)
    have delta:=difference index (by omega)
    simp only [sumPrefix]
    omega

/-- The actual decoded adjacent-word differences telescope. Aggregate payload
bytes are bounded once, rather than charging the whole slice for every item. -/
theorem Records.size_bounds (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length) :
    sumPrefix (fun index=>(recordLength input start length (decodedCount input start length) index).toNat)
      (decodedCount input start length)≤length ∧
    (∀ index<decodedCount input start length,
      (recordLength input start length (decodedCount input start length) index).toNat≤length) := by
  classical
  rcases records with empty|nonempty
  · simp [decodedCount,empty,sumPrefix]
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have lengthBound : length<2^64 := by have h:=plan.slice; rw [lengthEq] at h; have m:=Nat.mod_lt input.length (by decide : 0<2^64); omega
    have lengthWord : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthBound]
    have nonemptyLength : length≠0 := by have h:=plan.header; have p:=plan.positive; rw [lengthEq] at h; omega
    let count:=decodedCount input start length
    have countValue : count=plan.count := by simp only [count,decodedCount,if_neg nonemptyLength]; exact countEq.symm
    let offset:=recordOffset input start length count
    have ordered : ∀ index<count,offset index≤offset (index+1) := by
      intro index inside
      have this:=valid index (by rw [←countValue]; exact inside)
      have currentUpper : (currentWord input start index).toNat≤length := by simpa only [lengthWord] using this.2.1
      by_cases next : index+1<count
      · have later:=valid (index+1) (by rw [←countValue]; exact next)
        have increasing:=later.2.2 (by omega)
        simpa only [offset,recordOffset,if_pos inside,if_pos next,Nat.add_sub_cancel] using increasing
      · simpa only [offset,recordOffset,if_pos inside,if_neg next] using currentUpper
    have difference : ∀ index<count,(recordLength input start length count index).toNat=offset (index+1)-offset index := by
      intro index inside
      have order:=ordered index inside
      by_cases next : index+1<count
      · simp only [offset,recordOffset,if_pos inside,if_pos next] at order ⊢
        simp only [recordLength,if_pos next,BitVec.toNat_sub_of_le (show currentWord input start index≤currentWord input start (index+1) from order)]
      · simp only [offset,recordOffset,if_pos inside,if_neg next] at order ⊢
        have wordOrder : currentWord input start index≤BitVec.ofNat 64 length := by
          change (currentWord input start index).toNat≤(BitVec.ofNat 64 length).toNat
          rw [lengthWord]
          exact order
        simp only [recordLength,if_neg next,BitVec.toNat_sub_of_le wordOrder,lengthWord]
    have telescope:=prefix_telescope offset (fun index=>(recordLength input start length count index).toNat) count ordered difference count (Nat.le_refl _)
    have finalOffset : offset count=length := by simp [offset,recordOffset]
    change sumPrefix (fun index=>(recordLength input start length count index).toNat) count≤length ∧ _
    refine ⟨by rw [finalOffset] at telescope; omega,?_⟩
    intro index inside
    change (recordLength input start length count index).toNat≤length
    have delta:=difference index inside
    have upper : offset (index+1)≤length := by
      by_cases next : index+1<count
      · have later:=valid (index+1) (by rw [←countValue]; exact next)
        simpa only [offset,recordOffset,if_pos next,lengthWord] using later.2.1
      · simp only [offset,recordOffset,if_neg next]; exact Nat.le_refl _
    omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.prefix_telescope
#print axioms InitECandidate.Solver.Input.VarList.Records.size_bounds

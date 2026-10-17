import InitECandidate.Solver.Input.VarList.Records

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

def decodedCount (input : Guest.InputBlob) (start length : Nat) : Nat := if length=0 then 0 else Guest.GasLimit.le32 input start/4
def decodedArray (array : BitVec 64) (length : Nat) : BitVec 64 := if length=0 then 0#64 else array
def recordLength (input : Guest.InputBlob) (start length count index : Nat) : BitVec 64 :=
  (if index+1<count then currentWord input start (index+1) else BitVec.ofNat 64 length)-currentWord input start index

/-- Normal parsed records supply all real mapped length cells, including an
empty record array with no readable-address or positive-pointer premise. -/
theorem Records.cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (records : Records source input pointer array start length) :
    decodedCount input start length≤length/4 ∧ decodedCount input start length<2^31 ∧
      ∀ index<decodedCount input start length,
        source.memaddrs (lengthCell (decodedArray array length) index) ∧
        source.memory (lengthCell (decodedArray array length) index)=
          .word (recordLength input start length (decodedCount input start length) index) := by
  classical
  rcases records with empty|nonempty
  · simp [decodedCount,decodedArray,empty]
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have positive:=plan.positive
    have header:=plan.header
    have ne : length≠0 := by have h:=plan.length; rw [lengthEq] at header; omega
    simp only [decodedCount,decodedArray,if_neg ne]
    have bound : Guest.GasLimit.le32 input start/4≤length/4 := by rw [lengthEq,countEq] at header; omega
    have small : Guest.GasLimit.le32 input start/4<2^31 := by rw [←countEq]; exact plan.count_small
    refine ⟨bound,small,?_⟩
    intro index inside
    have planInside : index<plan.count := by rw [countEq]; exact inside
    have mapped:=plan.length_mapped source domain index planInside
    have value:=(complete index planInside).2
    refine ⟨by simpa only [arrayEq] using mapped,?_⟩
    simpa only [recordLength,arrayEq,startEq,countEq] using value

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.cells

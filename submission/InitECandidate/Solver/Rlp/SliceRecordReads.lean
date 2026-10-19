import InitECandidate.Solver.Rlp.SliceArrayModel
import InitECandidate.Solver.Rlp.ValidationWriteFrame

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

def itemPointer (pointer : BitVec 64) : List ListItem → Nat → BitVec 64
  | _,0 => pointer
  | [],_+1 => pointer
  | item::items,index+1 => itemPointer (pointer+item.total) items index

theorem Records.at (memory : BitVec 64 → HolWordLab 64) (array pointer : BitVec 64) (items : List ListItem)
    (records : Records memory array pointer items) (index : Nat) (item : ListItem) (selected : items[index]?=some item) :
    memory (array+BitVec.ofNat 64 (16*index))=.word (itemPointer pointer items index) ∧
      memory (array+BitVec.ofNat 64 (16*index)+8#64)=.word item.total := by
  induction items generalizing array pointer index with
  | nil => simp at selected
  | cons head items ih =>
    cases index with
    | zero =>
      have same : head=item := by simpa using selected
      subst item
      simpa only [Nat.mul_zero,BitVec.add_zero,itemPointer] using And.intro records.1 records.2.1
    | succ index =>
      have tailSelected : items[index]?=some item := by simpa using selected
      have actual := ih (array+16#64) (pointer+head.total) records.2.2 index tailSelected
      have address : array+16#64+BitVec.ofNat 64 (16*index)=array+BitVec.ofNat 64 (16*(index+1)) := by
        simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.add_assoc]
        rw [BitVec.add_comm (16#64 : BitVec 64)]
      rw [address] at actual
      exact actual

theorem Records.above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (items : List ListItem) (cutoff : Nat)
    (records : Records source.memory array pointer items) (frame : Validation.Above source target cutoff)
    (below : cutoff≤array.toNat) (fits : array.toNat+16*items.length<2^64) : Records target.memory array pointer items := by
  induction items generalizing array pointer with
  | nil => trivial
  | cons item items ih =>
    have lengthNumber : (array+8#64).toNat=array.toNat+8 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+8<2^64; simp only [List.length_cons] at fits; omega)]
      rfl
    have nextNumber : (array+16#64).toNat=array.toNat+16 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+16<2^64; simp only [List.length_cons] at fits; omega)]
      rfl
    refine ⟨(frame array below).trans records.1,(frame (array+8#64) (by rw [lengthNumber]; omega)).trans records.2.1,?_⟩
    exact ih (array+16#64) (pointer+item.total) records.2.2 (by rw [nextNumber]; omega)
      (by rw [nextNumber]; simp only [List.length_cons] at fits; omega)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Records.at
#print axioms InitECandidate.Solver.Rlp.Slices.Records.above

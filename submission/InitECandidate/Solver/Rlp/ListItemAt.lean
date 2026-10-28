import InitECandidate.Solver.Rlp.SliceRecordAt

namespace InitECandidate.Solver.Rlp
open Flapjack PanSemStateFiniteExact

theorem ListItem.total_eq_size (item : ListItem) : item.total=BitVec.ofNat 64 item.size := by
  simp only [ListItem.total,ListItem.size,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- Every selected actual item has a real offset inside the covered input
and retains its validated encoding at exactly that address. -/
theorem ListItems.at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (bytes : Nat) (items : List ListItem) (model : ListItems source pointer bytes items)
    (index : Nat) (item : ListItem) (selected : items[index]?=some item) :
    ∃ offset : Nat,Slices.itemPointer pointer items index=pointer+BitVec.ofNat 64 offset ∧ offset+item.size≤bytes ∧
      item.valid ∧ Header.Encoded source (pointer+BitVec.ofNat 64 offset) item.header item.payload item.flag := by
  induction model generalizing index item with
  | nil pointer => simp at selected
  | cons pointer head bytes items encoded valid rest ih =>
    cases index with
    | zero =>
      have same : head=item := by simpa using selected
      subst item
      refine ⟨0,by simp [Slices.itemPointer],by omega,valid,?_⟩
      simpa using encoded
    | succ index =>
      have tailSelected : items[index]?=some item := by simpa using selected
      obtain ⟨offset,path,bounded,itemValid,itemEncoded⟩ := ih index item tailSelected
      have address : pointer+head.total+BitVec.ofNat 64 offset=pointer+BitVec.ofNat 64 (head.size+offset) := by
        rw [head.total_eq_size,BitVec.ofNat_add,BitVec.add_assoc]
      refine ⟨head.size+offset,?_,by omega,itemValid,?_⟩
      · exact path.trans address
      · rw [←address]
        exact itemEncoded

theorem ListItems.at_span (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (bytes : Nat) (items : List ListItem) (model : ListItems source pointer bytes items)
    (index : Nat) (item : ListItem) (selected : items[index]?=some item) (fits : pointer.toNat+bytes<2^64) :
    item.total.toNat=item.size ∧ 1≤item.total.toNat ∧ item.total.toNat≤bytes ∧
      (Slices.itemPointer pointer items index).toNat+item.total.toNat<2^64 := by
  obtain ⟨offset,path,bounded,valid,encoded⟩ := model.at source pointer bytes items index item selected
  have positive := item.positive valid
  have small : item.size<2^64 := by omega
  have totalNumber : item.total.toNat=item.size := by rw [item.total_eq_size,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have offsetSmall : offset<2^64 := by omega
  have pointerNumber : (Slices.itemPointer pointer items index).toNat=pointer.toNat+offset := by
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  exact ⟨totalNumber,by rw [totalNumber]; exact positive,by rw [totalNumber]; omega,by rw [pointerNumber,totalNumber]; omega⟩

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.ListItem.total_eq_size
#print axioms InitECandidate.Solver.Rlp.ListItems.at
#print axioms InitECandidate.Solver.Rlp.ListItems.at_span

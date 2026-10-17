import InitECandidate.Solver.MutableTable.LayoutAddress32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack WitnessRadix

theorem copy_addresses (plan : AllocatedLayout.Plan) (key : BitVec 64) (index : Nat) (words : Fin 4→BitVec 64) :
    (Copy32.writes ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride) words).map Prod.fst=
      [cell plan .keys (32*index),cell plan .keys (32*index+8),cell plan .keys (32*index+16),cell plan .keys (32*index+24)] := by
  have first:=key_cell plan key index 0
  simp only [Nat.add_zero,BitVec.add_zero] at first
  simp only [Copy32.writes,List.map_cons,List.map_nil]
  rw [key_cell plan key index 8,key_cell plan key index 16,key_cell plan key index 24,first]

theorem metadata_addresses (plan : AllocatedLayout.Plan) (index count : Nat) :
    (Insert.countWrites (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 (base plan .order))
      (BitVec.ofNat 64 (base plan .position)) (BitVec.ofNat 64 index) (BitVec.ofNat 64 count)).map Prod.fst=
      [cell plan .order (8*count),cell plan .position (8*index),cell plan .header 24] := by
  have first:=scaled_cell plan .order 8 count 0
  have second:=scaled_cell plan .position 8 index 0
  simp only [Nat.add_zero,BitVec.add_zero] at first second
  simp only [Insert.countWrites,List.map_cons,List.map_nil,first,second]
  rw [← offset_cell plan .header 24]
  rfl

theorem copy_away (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index : Nat) (indexInside : index<plan.capacity) (words : Fin 4→BitVec 64)
    (pool : Pool) (offset : Nat) (inside : offset<size plan pool) (different : pool≠.keys) :
    cell plan pool offset∉(Copy32.writes ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride) words).map Prod.fst := by
  rw [copy_addresses]
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨separate plan ready pool .keys different offset (32*index) inside (by change _<32*plan.capacity;omega),
    separate plan ready pool .keys different offset (32*index+8) inside (by change _<32*plan.capacity;omega),
    separate plan ready pool .keys different offset (32*index+16) inside (by change _<32*plan.capacity;omega),
    separate plan ready pool .keys different offset (32*index+24) inside (by change _<32*plan.capacity;omega)⟩

theorem old_keys_copy_away (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index old byte : Nat) (indexInside : index<plan.capacity) (oldInside : old<plan.capacity) (different : old≠index)
    (byteInside : byte<32) (words : Fin 4→BitVec 64) :
    panByteAlignHOL (width:=64)
      ((parameters plan key).keys+BitVec.ofNat 64 old*(parameters plan key).stride+BitVec.ofNat 64 byte)∉
      (Copy32.writes ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride) words).map Prod.fst := by
  simp only [Copy32.writes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
  have first:=key_words_separate plan ready key old index byte 0 oldInside indexInside different byteInside (by decide)
  simp only [Nat.mul_zero,BitVec.add_zero] at first
  exact ⟨first,
    key_words_separate plan ready key old index byte 1 oldInside indexInside different byteInside (by decide),
    key_words_separate plan ready key old index byte 2 oldInside indexInside different byteInside (by decide),
    key_words_separate plan ready key old index byte 3 oldInside indexInside different byteInside (by decide)⟩

theorem metadata_away (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (index count : Nat) (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (pool : Pool) (offset : Nat) (inside : offset<size plan pool)
    (notOrder : pool≠.order) (notPosition : pool≠.position) (notCount : pool≠.header ∨ offset≠24) :
    cell plan pool offset∉(Insert.countWrites (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 (base plan .order))
      (BitVec.ofNat 64 (base plan .position)) (BitVec.ofNat 64 index) (BitVec.ofNat 64 count)).map Prod.fst := by
  rw [metadata_addresses]
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨separate plan ready pool .order notOrder offset (8*count) inside (by change _<8*plan.capacity;omega),
    separate plan ready pool .position notPosition offset (8*index) inside (by change _<8*plan.capacity;omega),?_⟩
  rcases notCount with different|different
  · exact separate plan ready pool .header different offset 24 inside (by change 24<72;decide)
  · by_cases same : pool=.header
    · subst pool;exact cell_injective plan ready .header offset 24 inside (by change 24<72;decide) different
    · exact separate plan ready pool .header same offset 24 inside (by change 24<72;decide)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.copy_away
#print axioms InitECandidate.Solver.MutableTable.Layout32.old_keys_copy_away
#print axioms InitECandidate.Solver.MutableTable.Layout32.metadata_away

import InitECandidate.Solver.MutableTable.Layout32
import InitECandidate.Solver.MutableTable.InsertFrame32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack WitnessRadix

def parameters:=TableEmpty.parameters

theorem scaled_cell (plan : AllocatedLayout.Plan) (pool : Pool) (scale index offset : Nat) :
    BitVec.ofNat 64 (base plan pool)+BitVec.ofNat 64 index*BitVec.ofNat 64 scale+BitVec.ofNat 64 offset=
      cell plan pool (scale*index+offset) := by
  simp only [cell,BitVec.ofNat_add,BitVec.ofNat_mul]
  ac_rfl

theorem key_cell (plan : AllocatedLayout.Plan) (key : BitVec 64) (index offset : Nat) :
    (parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride+BitVec.ofNat 64 offset=
      cell plan .keys (32*index+offset) := scaled_cell plan .keys 32 index offset

theorem value_cell (plan : AllocatedLayout.Plan) (index : Nat) :
    BitVec.ofNat 64 (base plan .values)+BitVec.ofNat 64 index*8#64=cell plan .values (8*index) := by
  simpa only [Nat.add_zero,BitVec.add_zero] using scaled_cell plan .values 8 index 0

theorem used_cell (plan : AllocatedLayout.Plan) (key : BitVec 64) (index : Nat) :
    (parameters plan key).used+BitVec.ofNat 64 index=cell plan .used index := offset_cell plan .used index

theorem key_byte_cell (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index byte : Nat) (inside : index<plan.capacity) (byteInside : byte<32) :
    panByteAlignHOL (width:=64)
      ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride+BitVec.ofNat 64 byte)=
      cell plan .keys (32*index+8*(byte/8)) := by
  rw [key_cell,byte_cell plan ready .keys (32*index+byte) (by change _<32*plan.capacity;omega)]
  congr 1
  omega

theorem used_byte_cell (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index : Nat) (inside : index<plan.capacity) :
    panByteAlignHOL (width:=64) ((parameters plan key).used+BitVec.ofNat 64 index)=cell plan .used (8*(index/8)) := by
  rw [used_cell,byte_cell plan ready .used index inside]

/-- Different slots own disjoint32-byte key regions, including partial byte
loads and every word of the real key-copy operation. -/
theorem key_words_separate (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (key : BitVec 64) (first second byte limb : Nat)
    (firstInside : first<plan.capacity) (secondInside : second<plan.capacity) (different : first≠second)
    (byteInside : byte<32) (limbInside : limb<4) :
    panByteAlignHOL (width:=64)
      ((parameters plan key).keys+BitVec.ofNat 64 first*(parameters plan key).stride+BitVec.ofNat 64 byte)≠
      (parameters plan key).keys+BitVec.ofNat 64 second*(parameters plan key).stride+BitVec.ofNat 64 (8*limb) := by
  rw [key_byte_cell plan ready key first byte firstInside byteInside,key_cell]
  apply cell_injective plan ready .keys _ _
    (by change _<32*plan.capacity;omega) (by change _<32*plan.capacity;omega) (by omega)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.key_byte_cell
#print axioms InitECandidate.Solver.MutableTable.Layout32.used_byte_cell
#print axioms InitECandidate.Solver.MutableTable.Layout32.key_words_separate

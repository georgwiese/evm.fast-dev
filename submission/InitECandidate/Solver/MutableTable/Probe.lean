import InitECandidate.Solver.WitnessRadix.WordBits
import Mathlib.Data.List.Nodup

namespace InitECandidate.Solver.MutableTable.Probe

/-- Natural slot visited by the actual masked linear increment. -/
def slot (capacity start index : Nat) : Nat:=(start+index)%capacity

theorem power_mask (word : BitVec 64) (bits : Nat) (small : bits<64) :
    (word &&& (BitVec.ofNat 64 (2^bits)-1#64)).toNat=word.toNat%(2^bits) := by
  have powerSmall : 2^bits<2^64:=Nat.pow_lt_pow_right (by decide) small
  have positive : 0<2^bits:=Nat.two_pow_pos bits
  have number : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt powerSmall]
  have atLeastOne : 1#64≤BitVec.ofNat 64 (2^bits) := by
    change (1#64).toNat≤(BitVec.ofNat 64 (2^bits)).toNat
    rw [number]
    change 1≤2^bits
    omega
  rw [BitVec.toNat_and,BitVec.toNat_sub_of_le atLeastOne,number]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat bits

theorem increment (word : BitVec 64) (bits : Nat) (small : bits<64) (inside : word.toNat<2^bits) :
    ((word+1#64) &&& (BitVec.ofNat 64 (2^bits)-1#64)).toNat=(word.toNat+1)%(2^bits) := by
  rw [power_mask _ bits small,BitVec.toNat_add_of_lt]
  · rfl
  · have powerSmall : 2^bits<2^64:=Nat.pow_lt_pow_right (by decide) small
    change word.toNat+1<2^64
    omega

theorem slot_number (capacity start index : Nat) (positive : 0<capacity) (startInside : start<capacity) (inside : index<capacity) :
    slot capacity start index=if start+index<capacity then start+index else start+index-capacity := by
  unfold slot
  by_cases first : start+index<capacity
  · rw [if_pos first,Nat.mod_eq_of_lt first]
  · rw [if_neg first,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]

theorem slot_injective (capacity start first second : Nat) (positive : 0<capacity) (startInside : start<capacity)
    (firstInside : first<capacity) (secondInside : second<capacity)
    (same : slot capacity start first=slot capacity start second) : first=second := by
  rw [slot_number capacity start first positive startInside firstInside,
    slot_number capacity start second positive startInside secondInside] at same
  split at same <;> split at same <;> omega

def visited (capacity start count : Nat) : List Nat:=(List.range count).map (slot capacity start)

theorem visited_distinct (capacity start count : Nat) (positive : 0<capacity) (startInside : start<capacity)
    (bounded : count≤capacity) : (visited capacity start count).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro first firstMember second secondMember same
  have firstSmall : first<count:=List.mem_range.mp firstMember
  have secondSmall : second<count:=List.mem_range.mp secondMember
  exact slot_injective capacity start first second positive startInside (by omega) (by omega) same

/-- Any prefix of occupied probes visits different slots. If all occupied
slots appear in the actual order array, its length bounds occupied probes.
Establishing order/used-array correspondence is a separate table invariant. -/
theorem occupied_prefix_bound (capacity start count : Nat) (order : List Nat)
    (positive : 0<capacity) (startInside : start<capacity) (bounded : count≤capacity)
    (covered : ∀ index<count,slot capacity start index∈order) : count≤order.length := by
  have distinct:=visited_distinct capacity start count positive startInside bounded
  have subset : visited capacity start count⊆order := by
    intro value member
    obtain ⟨index,member,same⟩:=List.mem_map.mp member
    rw [← same]
    exact covered index (List.mem_range.mp member)
  have lengths:=List.Nodup.length_le_of_subset distinct subset
  simpa only [visited,List.length_map,List.length_range] using lengths

/-- A table with fewer occupied slots than capacity cannot have a full cycle
of occupied probes, independently of the hash distribution. -/
theorem empty_within_count (capacity start : Nat) (order : List Nat) (used : Nat→Prop)
    (positive : 0<capacity) (startInside : start<capacity) (room : order.length<capacity)
    (covered : ∀ index,used index→index∈order) :
    ∃ index≤order.length,¬used (slot capacity start index) := by
  classical
  by_contra missing
  have occupied : ∀ index<order.length+1,slot capacity start index∈order := by
    intro index inside
    apply covered
    by_contra empty
    exact missing ⟨index,by omega,empty⟩
  have impossible:=occupied_prefix_bound capacity start (order.length+1) order positive startInside (by omega) occupied
  omega

end InitECandidate.Solver.MutableTable.Probe

#print axioms InitECandidate.Solver.MutableTable.Probe.power_mask
#print axioms InitECandidate.Solver.MutableTable.Probe.increment
#print axioms InitECandidate.Solver.MutableTable.Probe.slot_injective
#print axioms InitECandidate.Solver.MutableTable.Probe.visited_distinct
#print axioms InitECandidate.Solver.MutableTable.Probe.occupied_prefix_bound
#print axioms InitECandidate.Solver.MutableTable.Probe.empty_within_count

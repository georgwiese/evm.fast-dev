import InitECandidate.Solver.MutableTable.MemoryModelAppend

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem empty_slot_fresh (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (occupied : Occupied source kind plan slots) (index : BitVec 64) (inside : index.toNat < plan.capacity)
    (empty : Find.usedByte source (parameters kind plan 0#64) index = some 0) : index.toNat ∉ slots := by
  intro member
  have actual := occupied.used index.toNat inside
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, if_pos member] at actual
  rw [empty] at actual
  simp at actual

/-- Complete physical occupied/order/inverse-position invariant after the
actual generic raw-insertion memory formula. The inserted slot was empty;
no logical key relation, collision assumption or mutation execution is given. -/
theorem Occupied.after_insert (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : Occupied source kind plan slots)
    (query index value : BitVec 64) (inside : index.toNat < plan.capacity)
    (empty : Find.usedByte source (parameters kind plan 0#64) index = some 0) :
    Occupied {source with memory := insertedMemory source.memory source.be kind plan query index (BitVec.ofNat 64 slots.length) value}
      kind plan (slots ++ [index.toNat]) := by
  let count := BitVec.ofNat 64 slots.length
  let post := {source with memory := insertedMemory source.memory source.be kind plan query index count value}
  have lengthSmall : slots.length < 2 ^ 64 := Nat.lt_trans room (capacity_small kind plan valid)
  have countNat : count.toNat = slots.length := by
    change slots.length % 2 ^ 64 = slots.length
    exact Nat.mod_eq_of_lt lengthSmall
  have countInside : count.toNat < plan.capacity := by rw [countNat]; exact room
  have fresh := empty_slot_fresh source kind plan slots occupied index inside empty
  refine ⟨append_distinct slots index.toNat occupied.distinct fresh, ?_, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact occupied.inside slot old
    · exact inside
  · intro slot slotInside
    have slotSmall : slot < 2 ^ 64 := Nat.lt_trans slotInside (capacity_small kind plan valid)
    have vectorInside : (BitVec.ofNat 64 slot).toNat < plan.capacity := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt slotSmall]
      exact slotInside
    have written := inserted_used source kind plan valid domain little query index count value (BitVec.ofNat 64 slot) inside countInside vectorInside
    by_cases same : slot = index.toNat
    · have vectorSame : BitVec.ofNat 64 slot = index := by simp [same]
      rw [if_pos vectorSame] at written
      simpa [List.mem_append, List.mem_singleton, same] using written
    · have vectorDifferent : BitVec.ofNat 64 slot ≠ index := by
        intro equal
        have numeric := congrArg BitVec.toNat equal
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt slotSmall] at numeric
        exact same numeric
      rw [if_neg vectorDifferent, occupied.used slot slotInside] at written
      simpa [List.mem_append, List.mem_singleton, same] using written
  · intro item
    have itemInside : item.val < plan.capacity := by
      have high := item.isLt
      simp only [List.length_append, List.length_singleton] at high
      omega
    have written := inserted_order source.memory source.be kind plan valid query index count value inside countInside item.val itemInside
    by_cases old : item.val < slots.length
    · rw [append_get_old slots index.toNat item old]
      change insertedMemory source.memory source.be kind plan query index count value (cell plan .order (8 * item.val)) = _
      rw [written, countNat, if_neg (show item.val ≠ slots.length from by omega)]
      exact occupied.order ⟨item.val, old⟩
    · have last : item.val = slots.length := by
        have high := item.isLt
        simp only [List.length_append, List.length_singleton] at high
        omega
      rw [append_get_new slots index.toNat item last]
      change insertedMemory source.memory source.be kind plan query index count value (cell plan .order (8 * item.val)) = _
      simpa only [countNat, if_pos last, BitVec.ofNat_toNat, BitVec.setWidth_eq] using written
  · intro item
    by_cases old : item.val < slots.length
    · let prior : Fin slots.length := ⟨item.val, old⟩
      have slotInside := occupied.inside (slots.get prior) (List.get_mem slots prior)
      have different : slots.get prior ≠ index.toNat := by
        intro equal
        apply fresh
        rw [← equal]
        exact List.get_mem slots prior
      rw [append_get_old slots index.toNat item old]
      change insertedMemory source.memory source.be kind plan query index count value (cell plan .position (8 * slots.get prior)) = _
      rw [inserted_position source.memory source.be kind plan valid query index count value inside countInside _ slotInside, if_neg different]
      exact occupied.position prior
    · have last : item.val = slots.length := by
        have high := item.isLt
        simp only [List.length_append, List.length_singleton] at high
        omega
      rw [append_get_new slots index.toNat item last]
      change insertedMemory source.memory source.be kind plan query index count value (cell plan .position (8 * index.toNat)) = _
      rw [inserted_position source.memory source.be kind plan valid query index count value inside countInside _ inside, if_pos rfl, last]

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.empty_slot_fresh
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Occupied.after_insert

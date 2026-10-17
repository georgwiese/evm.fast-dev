import InitECandidate.Solver.MutableTable.NaturalLayoutOwnership

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The nine physical words of the unchanged table header. -/
def headerEntries (kind : KeyHash.Kind) (plan : Plan) (count : BitVec 64) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (KeyHash.keySize kind)), (8, BitVec.ofNat 64 (stride kind)),
   (16, BitVec.ofNat 64 plan.capacity), (24, count), (32, cell plan .keys 0),
   (40, cell plan .values 0), (48, cell plan .used 0), (56, cell plan .order 0), (64, cell plan .position 0)]

def Header (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (count : BitVec 64) : Prop :=
  ∀ offset value, (offset, value) ∈ headerEntries kind plan count → memory (cell plan .header offset) = .word value

/-- Runtime representation of occupied slots and the real dense order/
position arrays. It contains no key-equality or cryptographic assumption. -/
structure Occupied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) : Prop where
  distinct : slots.Nodup
  inside : ∀ slot ∈ slots, slot < plan.capacity
  used : ∀ slot < plan.capacity, Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) =
    some (if slot ∈ slots then 1 else 0)
  order : ∀ index : Fin slots.length, source.memory (cell plan .order (8 * index.val)) = .word (BitVec.ofNat 64 (slots.get index))
  position : ∀ index : Fin slots.length, source.memory (cell plan .position (8 * slots.get index)) = .word (BitVec.ofNat 64 index.val)

/-- Physical header reads/maps for the original lookup ABI, derived from
owned pools and the actual nine-word header representation. -/
theorem Header.find_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (query count : BitVec 64)
    (header : Header source.memory kind plan count) :
    Find.HeaderData source (cell plan .header 0) (parameters kind plan query) := by
  have physical (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) :
      source.memaddrs (cell plan .header 0 + BitVec.ofNat 64 offset) := by
    rw [domain, constant_cell]
    exact mapped kind plan valid .header offset inside aligned
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact physical _ (by decide) (by decide)
  · rw [constant_cell]
    exact header 16 _ (by simp [headerEntries, parameters])
  · exact header 0 _ (by simp [headerEntries, parameters])
  · rw [constant_cell]
    exact header 8 _ (by simp [headerEntries, parameters])
  · rw [constant_cell]
    exact header 32 _ (by simp [headerEntries, parameters])
  · rw [constant_cell]
    exact header 48 _ (by simp [headerEntries, parameters])

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Header.find_data

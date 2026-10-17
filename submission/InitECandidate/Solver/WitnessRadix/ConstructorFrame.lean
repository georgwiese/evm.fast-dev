import InitECandidate.Solver.WitnessRadix.ConstructorMemory

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

def suffixState {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (index : Nat) (words : Fin 4 → BitVec 64) : PanSemStateFiniteExact 64 F :=
  storesPost (copyPost source layout.keys (BitVec.ofNat 64 index) words)
    layout.vals layout.primary layout.records (BitVec.ofNat 64 index)

def PrefixOffset (index : Nat) : Pool → Nat → Prop
  | .header, _ | .records, _ | .backup, _ => True
  | .keys, offset => offset < 32 * index
  | .vals, offset | .primary, offset => offset < 8 * index

theorem prefix_absent (index : Nat) (entry : Address)
    (preserve : PrefixOffset index entry.1 entry.2) : entry ∉ writeAddresses index := by
  obtain ⟨pool, offset⟩ := entry
  cases pool <;> simp [writeAddresses, PrefixOffset] at preserve ⊢ <;> omega

theorem prefix_memory (memory : WordWrites.Memory) (layout : Layout) (valid : Valid layout)
    (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64)
    (entry : Address) (bound : entry.2 < size layout entry.1)
    (preserve : PrefixOffset index entry.1 entry.2) :
    WordWrites.write memory (writes layout index words) (address layout entry) = memory (address layout entry) :=
  memory_away memory layout valid index inside words entry bound (prefix_absent index entry preserve)

theorem suffix_memory_preserved {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64)
    (entry : Address) (bound : entry.2 < size layout entry.1)
    (preserve : PrefixOffset index entry.1 entry.2) :
    (suffixState source layout index words).memory (address layout entry) = source.memory (address layout entry) := by
  rw [suffixState, suffix_memory]
  exact prefix_memory _ layout valid index inside words entry bound preserve

theorem suffix_hash_preserved {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64)
    (old : Nat) (older : old < index) (key : ByteKeys.Key)
    (view : MemoryBytes.ByteView source (layout.keys + BitVec.ofNat 64 old * 32#64) key) :
    MemoryBytes.ByteView (suffixState source layout index words)
      (layout.keys + BitVec.ofNat 64 old * 32#64) key := by
  apply MemoryBytes.byteView_of_cells source (suffixState source layout index words) rfl rfl _ _ _ view
  intro byte
  rw [hash_byte_cell layout valid old (by omega) byte]
  apply Eq.symm
  exact suffix_memory_preserved source layout valid index inside words
    (.keys, 32 * old + 8 * (byte.val / 8)) (by
      change 32 * old + 8 * (byte.val / 8) < 32 * layout.capacity
      have room := valid.room; have := byte.isLt; omega) (by
      change 32 * old + 8 * (byte.val / 8) < 32 * index
      have := byte.isLt; omega)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prefix_memory
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_memory_preserved
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_hash_preserved

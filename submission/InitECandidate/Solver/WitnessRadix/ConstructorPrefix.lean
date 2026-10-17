import InitECandidate.Solver.WitnessRadix.ConstructorFrame

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

/-- Precisely the initialized prefixes of the constructor's three arrays. -/
structure Prefix {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (done : Nat) : Prop where
  recordWords : ∀ index < done, source.memory (cell layout .vals (8 * index)) = .word (record layout index)
  hashViews : ∀ index < done,
    MemoryBytes.ByteView source (layout.keys + BitVec.ofNat 64 index * 32#64) (keyFor (BitVec.ofNat 64 index))
  ordinalWords : ∀ index < done, source.memory (cell layout .primary (8 * index)) = .word (BitVec.ofNat 64 index)

theorem prefix_empty {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) : Prefix source layout keyFor 0 := by
  constructor <;> intro index inside <;> omega

theorem suffix_word_view {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout) (index : Nat) (inside : index < layout.count)
    (words : Fin 4 → BitVec 64) : MemoryBytes.WordView (suffixState source layout index words)
      (layout.keys + BitVec.ofNat 64 index * 32#64) words := by
  refine ⟨?_, ?_⟩
  · intro limb
    change source.memaddrs _
    rw [hash_limb_cell]
    apply mapped .keys (32 * index + 8 * limb.val) (by omega)
    change 32 * index + 8 * limb.val + 8 ≤ 32 * layout.capacity
    have := limb.isLt; have room := valid.room; omega
  · intro limb
    rw [hash_limb_cell]
    change (storesPost _ _ _ _ _).memory _ = _
    rw [suffix_memory]
    exact WordWrites.write_unique source.memory _ _ (writes_distinct layout valid index inside words)
      (hash_member layout index words limb)

theorem prefix_step {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout) (keyFor : BitVec 64 → ByteKeys.Key)
    (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64)
    (prefixData : Prefix source layout keyFor index) (little : source.be = false)
    (currentKey : WordKeys.key words = keyFor (BitVec.ofNat 64 index)) :
    Prefix (suffixState source layout index words) layout keyFor (index + 1) := by
  have room := valid.room
  refine ⟨?_, ?_, ?_⟩
  · intro old bound
    by_cases same : old = index
    · subst old
      change (storesPost _ _ _ _ _).memory _ = _
      rw [suffix_memory]
      exact record_value_written _ layout valid index inside words
    · have older : old < index := by omega
      have frame := suffix_memory_preserved source layout valid index inside words (.vals, 8 * old)
        (by change 8 * old < 8 * layout.capacity; omega) (by change 8 * old < 8 * index; omega)
      exact frame.trans (prefixData.recordWords old older)
  · intro old bound
    by_cases same : old = index
    · subst old
      rw [← currentKey]
      exact MemoryBytes.wordView_bytes _ _ words (hash_aligned layout valid index inside)
        (hash_fits layout valid index inside) little (suffix_word_view source layout valid mapped index inside words)
    · exact suffix_hash_preserved source layout valid index inside words old (by omega) _ (prefixData.hashViews old (by omega))
  · intro old bound
    by_cases same : old = index
    · subst old
      change (storesPost _ _ _ _ _).memory _ = _
      rw [suffix_memory]
      exact ordinal_written _ layout valid index inside words
    · have older : old < index := by omega
      have frame := suffix_memory_preserved source layout valid index inside words (.primary, 8 * old)
        (by change 8 * old < 8 * layout.capacity; omega) (by change 8 * old < 8 * index; omega)
      exact frame.trans (prefixData.ordinalWords old older)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_word_view
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prefix_step

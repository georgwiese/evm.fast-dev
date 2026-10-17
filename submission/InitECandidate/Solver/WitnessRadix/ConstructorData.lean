import InitECandidate.Solver.WitnessRadix.ConstructorPrefix
import InitECandidate.Solver.WitnessRadix.BuildInitialize

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

/-- Header and original record slices, independent of initialization progress. -/
structure FixedData {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (sliceFor : BitVec 64 → Graph.Slice) : Prop where
  header : BuildEntry.Header source layout.table layout.keys layout.vals layout.primary layout.backup
  pointers : ∀ index < layout.count,
    source.memory (cell layout .records (16 * index)) = .word (sliceFor (BitVec.ofNat 64 index)).1
  lengths : ∀ index < layout.count,
    source.memory (cell layout .records (16 * index + 8)) = .word (sliceFor (BitVec.ofNat 64 index)).2

theorem suffix_fixed_data {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (sliceFor : BitVec 64 → Graph.Slice) (index : Nat)
    (inside : index < layout.count) (words : Fin 4 → BitVec 64) (fixedData : FixedData source layout sliceFor) :
    FixedData (suffixState source layout index words) layout sliceFor := by
  have headerFrame (offset : Nat) (bound : offset < 72) :
      (suffixState source layout index words).memory (cell layout .header offset) =
        source.memory (cell layout .header offset) :=
    suffix_memory_preserved source layout valid index inside words (.header, offset) bound True.intro
  refine ⟨⟨fixedData.header.keysMapped, ?_, fixedData.header.valsMapped, ?_,
    fixedData.header.srcMapped, ?_, fixedData.header.dstMapped, ?_⟩, ?_, ?_⟩
  · exact (headerFrame 32 (by decide)).trans fixedData.header.keysWord
  · exact (headerFrame 40 (by decide)).trans fixedData.header.valsWord
  · exact (headerFrame 56 (by decide)).trans fixedData.header.srcWord
  · exact (headerFrame 64 (by decide)).trans fixedData.header.dstWord
  · intro old bound
    exact (suffix_memory_preserved source layout valid index inside words (.records, 16 * old)
      (by change 16 * old < 16 * layout.count; omega) True.intro).trans (fixedData.pointers old bound)
  · intro old bound
    exact (suffix_memory_preserved source layout valid index inside words (.records, 16 * old + 8)
      (by change 16 * old + 8 < 16 * layout.count; omega) True.intro).trans (fixedData.lengths old bound)

/-- On loop completion the accumulated concrete prefix supplies every
immutable leaf-cell and key-byte premise required by the proved radix helper. -/
theorem immutable_from_prefix {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (fixedData : FixedData source layout sliceFor) (prefixData : Prefix source layout keyFor layout.count) :
    Immutable source layout keyFor sliceFor := by
  have room := valid.room
  refine ⟨fixedData.header.keysMapped, fixedData.header.keysWord,
    fixedData.header.valsMapped, fixedData.header.valsWord, ?_, prefixData.recordWords,
    ?_, ?_, fixedData.pointers, fixedData.lengths, prefixData.hashViews⟩
  · intro index inside
    apply mapped .vals (8 * index) (by omega)
    change 8 * index + 8 ≤ 8 * layout.capacity
    omega
  · intro index inside
    apply mapped .records (16 * index) (by omega)
    change 16 * index + 8 ≤ 16 * layout.count
    omega
  · intro index inside
    apply mapped .records (16 * index + 8) (by omega)
    change 16 * index + 8 + 8 ≤ 16 * layout.count
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_fixed_data
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.immutable_from_prefix

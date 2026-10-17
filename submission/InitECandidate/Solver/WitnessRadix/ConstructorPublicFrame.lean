import InitECandidate.Solver.WitnessRadix.ConstructorFrame

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

/-- The actual copy and metadata suffix preserves every public word that
precedes its written pools, independently of old private table contents. -/
theorem suffix_memory_before {F : Type} (source : PanSemStateFiniteExact 64 F)
    (layout : Layout) (valid : Valid layout) (index : Nat) (inside : index < layout.count)
    (words : Fin 4 → BitVec 64) (query : BitVec 64)
    (before : ∀ entry ∈ writeAddresses index, query.toNat < (base layout entry.1).toNat) :
    (suffixState source layout index words).memory query = source.memory query := by
  rw [suffixState, suffix_memory]
  apply WordWrites.write_away
  rw [write_cells]
  intro member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  have bound := write_bounds layout valid index inside entry entryMember
  have nowrap := valid.noWrap entry.1
  have number := byteAddress_toNat (base layout entry.1) entry.2 (by omega)
  have equalNumber := congrArg BitVec.toNat same
  change (byteAddress (base layout entry.1) entry.2).toNat = query.toNat at equalNumber
  rw [number] at equalNumber
  have low := before entry entryMember
  omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_memory_before

import InitECandidate.Solver.MutableTable.MemoryModelInsertFrame
import InitECandidate.Solver.MutableTable.NaturalLayoutRelocatedBounds

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Every original array word needed later by rehash survives an insertion
into the new arrays. The header stays at its actual old address; only its
count field may change. Allocation separation is a natural address fact. -/
theorem rehash_old_array (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat)
    (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (query index count value : BitVec 64) (inside : index.toNat < capacity) (countInside : count.toNat < capacity)
    (pool : Pool) (array : pool ≠ .header) (offset : Nat) (oldInside : offset < size kind old pool) :
    insertedMemory memory be kind (relocated kind (old.base .header) start capacity) query index count value (cell old pool offset) =
      memory (cell old pool offset) := by
  apply inserted_away memory be kind _ newValid query index count value _ inside countInside
  · intro newPool newArray newOffset newInside
    apply relocated_array_away kind (old.base .header) start capacity newValid _ _ newPool newArray newOffset newInside
    left
    rw [number kind old oldValid pool offset oldInside]
    have high := earlier pool
    omega
  · exact separate kind old oldValid pool .header array offset 24 oldInside (by change 24 < 72; decide)

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.rehash_old_array

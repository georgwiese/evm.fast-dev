import InitECandidate.Solver.WitnessRadix.OpenGraphReplace

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

def leafPost {F : Type} (source : PanSemStateFiniteExact 64 F) (address : BitVec 64) (ordinal : Nat) :
    PanSemStateFiniteExact 64 F :=
  { source with memory := StoreWord.put source.memory address (WordBits.leafTag ordinal) }

/-- A terminal tag store fills a hole with the final ordinal's actual key and
record slice, while preserving all of that leaf's read-only cells. -/
theorem new_leaf {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals address record pointer length : BitVec 64) (ordinal : Nat) (key : ByteKeys.Key)
    (small : ordinal < 2 ^ 63) (mapped : source.memaddrs address)
    (cells : QueryLeaf.LeafCells source table keys vals (BitVec.ofNat 64 ordinal) record pointer length)
    (view : MemoryBytes.ByteView source (keys + BitVec.ofNat 64 ordinal * 32#64) key)
    (fits : (keys + BitVec.ofNat 64 ordinal * 32#64).toNat + 32 < 2 ^ 64)
    (away : ∀ query, QueryMemory.reads source table keys vals (WordBits.leafTag ordinal) (.leaf key (pointer, length)) query →
      query ≠ address) :
    Represents (leafPost source address ordinal) table keys vals
      (.complete address (WordBits.leafTag ordinal) (.leaf key (pointer, length))) := by
  have rep : QueryMemory.Represents source table keys vals (WordBits.leafTag ordinal) (.leaf key (pointer, length)) :=
    ⟨ordinal, record, small, rfl, cells, view, fits⟩
  refine ⟨mapped, ?_, QueryMemory.represents_of_agreement source (leafPost source address ordinal)
    rfl rfl table keys vals _ _ ?_ rep⟩
  · simp [leafPost, StoreWord.put]
  · intro query member
    change source.memory query = StoreWord.put source.memory address (WordBits.leafTag ordinal) query
    simp [StoreWord.put, away query member]

/-- Install that leaf at any selected frontier hole, retaining the represented
ancestors and completed siblings under an explicit outside-read condition. -/
theorem fill_leaf {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals address record pointer length : BitVec 64) (ordinal : Nat) (key : ByteKeys.Key)
    (before after : Tree)
    (step : ReplaceHole address (.leaf key (pointer, length))
      (.complete address (WordBits.leafTag ordinal) (.leaf key (pointer, length))) before after)
    (oldRep : Represents source table keys vals before)
    (small : ordinal < 2 ^ 63) (mapped : source.memaddrs address)
    (cells : QueryLeaf.LeafCells source table keys vals (BitVec.ofNat 64 ordinal) record pointer length)
    (view : MemoryBytes.ByteView source (keys + BitVec.ofNat 64 ordinal * 32#64) key)
    (fits : (keys + BitVec.ofNat 64 ordinal * 32#64).toNat + 32 < 2 ^ 64)
    (leafAway : ∀ query, QueryMemory.reads source table keys vals (WordBits.leafTag ordinal) (.leaf key (pointer, length)) query →
      query ≠ address)
    (oldAway : ∀ query, reads source table keys vals before query → query ≠ address) :
    Represents (leafPost source address ordinal) table keys vals after ∧ expected after = expected before := by
  refine ⟨replacement_represents source (leafPost source address ordinal) rfl rfl table keys vals step rfl
    (new_leaf source table keys vals address record pointer length ordinal key small mapped cells view fits leafAway)
    ?_ oldRep, replacement_expected step rfl⟩
  intro query member
  change source.memory query = StoreWord.put source.memory address (WordBits.leafTag ordinal) query
  simp [StoreWord.put, oldAway query member]

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.new_leaf
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.fill_leaf

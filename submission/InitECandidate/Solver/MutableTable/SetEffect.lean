import InitECandidate.Solver.MutableTable.InsertSelection
import InitECandidate.Solver.MutableTable.InsertGeneralCall

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The two physical memory effects of a setter without growth. The selected
update slot is occupied; a newly inserted slot was actually empty. This says
nothing about logical key equality or favorable hash behavior. -/
def Effect (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (p : Find.Parameters)
    (table vals order position count value : BitVec 64) (memory : WordWrites.Memory) : Prop :=
  (∃ index : BitVec 64, index.toNat < p.capacity.toNat ∧ Find.usedByte source p index = some 1 ∧
    memory = StoreWord.put source.memory (vals + index * 8#64) value) ∨
  (∃ index : BitVec 64, index.toNat < p.capacity.toNat ∧ Find.usedByte source p index = some 0 ∧
    memory = Insert.generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position index count value)

theorem Effect.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (p : Find.Parameters)
    (table vals order position count value : BitVec 64) (memory : WordWrites.Memory)
    (sameMemory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (effect : Effect source kind p table vals order position count value memory) :
    Effect target kind p table vals order position count value memory := by
  rcases effect with ⟨index, inside, used, stored⟩ | ⟨index, inside, used, stored⟩
  · refine Or.inl ⟨index, inside, ?_, ?_⟩
    · rw [← Find.usedByte_of_fields source target p index sameMemory domain endian]
      exact used
    · rw [← sameMemory]
      exact stored
  · refine Or.inr ⟨index, inside, ?_, ?_⟩
    · rw [← Find.usedByte_of_fields source target p index sameMemory domain endian]
      exact used
    · rw [← sameMemory, ← endian]
      exact stored

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.Effect.of_fields

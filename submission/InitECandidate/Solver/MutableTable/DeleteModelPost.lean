import InitECandidate.Solver.MutableTable.DeletePresent

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

structure ModelPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat)
    (paid : Nat) (memory : WordWrites.Memory) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (next : List Nat) (flag : BitVec 64) : Prop where
  frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid}
  shape : (flag = 0#64 ∧ memory = source.memory ∧ next = slots) ∨ (flag = 1#64 ∧ next.length + 1 = slots.length)
  header : MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length)
  occupied : MemoryModel.Occupied target kind plan next

theorem ModelPost.count_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat)
    (paid : Nat) (memory : WordWrites.Memory) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (next : List Nat) (flag : BitVec 64)
    (post : ModelPost source kind plan slots paid memory target next flag) : slots.length - 1 ≤ next.length ∧ next.length ≤ slots.length := by
  rcases post.shape with ⟨_, _, rfl⟩ | ⟨_, length⟩ <;> omega

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.ModelPost.count_bound

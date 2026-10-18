import InitECandidate.Solver.MutableTable.DeletePending

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The real physical table model initializes the hole invariant without a
memory mutation or assumptions about hash distribution/key uniqueness. -/
theorem initial_pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length) :
    Pending source kind plan slots.length deleted (Function.update (fun index : Fin slots.length => slots.get index) deleted plan.capacity) (slots.get deleted) := by
  classical
  let original := fun index : Fin slots.length => slots.get index
  have distinct : Function.Injective original := fun _ _ same => occupied.distinct.get_inj_iff.mp same
  have oldInside (index : Fin slots.length) : original index < plan.capacity := occupied.inside (slots.get index) (List.get_mem slots index)
  have fresh : ∀ index, original index ≠ plan.capacity := fun index => Nat.ne_of_lt (oldInside index)
  have holeDifferent : plan.capacity ≠ original deleted := Nat.ne_of_gt (oldInside deleted)
  refine ⟨room, entries_update_injective original distinct deleted plan.capacity fresh, ?_, ?_, oldInside deleted,
    entries_update_fresh original distinct deleted plan.capacity (original deleted) rfl holeDifferent, ?_, ?_, ?_, ?_⟩
  · simp [Function.update]
  · intro index active
    simpa only [Function.update_of_ne active] using oldInside index
  · intro slot inside
    have actual := occupied.used slot inside
    by_cases member : slot ∈ slots
    · exact Or.inr (by simpa only [if_pos member] using actual)
    · exact Or.inl (by simpa only [if_neg member] using actual)
  · intro slot inside
    rw [occupied.used slot inside, covered_initial slots deleted plan.capacity slot]
    by_cases member : slot ∈ slots <;> simp [member]
  · intro index active
    simpa only [Function.update_of_ne active] using occupied.order index
  · intro index active
    simpa only [Function.update_of_ne active] using occupied.position index

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.initial_pending

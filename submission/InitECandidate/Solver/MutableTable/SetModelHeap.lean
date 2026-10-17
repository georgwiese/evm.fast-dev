import InitECandidate.Solver.MutableTable.SetModelBudget

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old : Plan} {start count paid : Nat}
  {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {target : PanSemStateFiniteExact 64 Guest.HostMemory}
  {plan : Plan} {slots : List Nat}

theorem ModelPost.capacity_shape (post : ModelPost source kind old start count paid globals memory target plan slots) :
    old.capacity ≤ plan.capacity ∧ (plan.capacity = old.capacity ∨ plan.capacity = 2 * old.capacity) := by
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact ⟨Nat.le_refl _, Or.inl rfl⟩
  · exact ⟨by change old.capacity ≤ 2 * old.capacity; omega, Or.inr rfl⟩

/-- Every actual capacity increase is controlled by the observed item count,
not an unrelated address-space maximum. This supports bounds in terms of the
maximum population reached, including executions that later delete items. -/
theorem ModelPost.growth_count_bound (post : ModelPost source kind old start count paid globals memory target plan slots)
    (changed : plan ≠ old) : plan.capacity < 4 * (slots.length + 1) := by
  have threshold := post.grew changed
  have lower := post.countBound.1
  rcases post.shape with ⟨same, _⟩ | ⟨rfl, _⟩
  · exact (changed same).elim
  · change 2 * old.capacity < 4 * (slots.length + 1)
    omega

/-- The returned table still has an original power-of-two capacity and the
same minimum four. No new probe-power premise is needed at the next caller. -/
theorem ModelPost.next_power (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind old) (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits) :
    ∃ nextBits, nextBits < 64 ∧ 2 ≤ nextBits ∧ plan.capacity = 2 ^ nextBits := by
  obtain ⟨small, doubled, _⟩ := MemoryModel.growth_shape kind old valid bits power minimum
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact ⟨bits, by omega, minimum, power⟩
  · exact ⟨bits + 1, small, by omega, doubled⟩

/-- The actual post-call heap word is the old cursor or the end of exactly
five new arrays. All current table pools remain below that cursor, so the
next mutation can reuse the same natural allocation-separation invariant. -/
theorem ModelPost.next_heap (post : ModelPost source kind old start count paid globals memory target plan slots)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start)))) :
    ∃ nextCursor, (nextCursor = start ∨ nextCursor = relocatedEnd kind start (2 * old.capacity)) ∧ start ≤ nextCursor ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 nextCursor))) ∧
      ∀ pool, plan.base pool + size kind plan pool ≤ nextCursor := by
  have globalsEq := congrArg PanSemStateFiniteExact.globals post.frame
  change target.globals = globals at globalsEq
  rcases post.shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨start, Or.inl rfl, Nat.le_refl _, by rw [globalsEq]; exact heap, earlier⟩
  · have forward : start ≤ relocatedEnd kind start (2 * old.capacity) := by dsimp only [relocatedEnd]; omega
    refine ⟨relocatedEnd kind start (2 * old.capacity), Or.inr rfl, forward, ?_, ?_⟩
    · rw [globalsEq]
      simp [HolFiniteMapExact.update, FUPDATE]
    · intro pool
      by_cases header : pool = .header
      · subst pool
        have before := earlier .header
        change old.base .header + 72 ≤ start at before
        change old.base .header + 72 ≤ relocatedEnd kind start (2 * old.capacity)
        omega
      · exact (relocated_array_bounds kind (old.base .header) start (2 * old.capacity) pool header).2

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.capacity_shape
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.growth_count_bound
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.next_power
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.next_heap

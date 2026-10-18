import InitECandidate.Solver.MutableTable.SetModelOwnership

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang

variable {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old plan : Plan}
  {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}

theorem ModelPost.header_pointer (post : ModelPost source kind old start count paid globals memory target plan slots) :
    cell plan .header 0 = cell old .header 0 := by
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl

/-- The reached post-layout supplies the bounds and alignment of its real
heap cursor, including the growth case. No future allocation is assumed. -/
theorem ModelPost.cursor (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind plan) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start)))) :
    ∃ cursor, start ≤ cursor ∧ cursor ≤ 33806089496 ∧ cursor % 8 = 0 ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) ∧
      ∀ pool, plan.base pool + size kind plan pool ≤ cursor := by
  have globalsEq := congrArg PanSemStateFiniteExact.globals post.frame
  change target.globals = globals at globalsEq
  rcases post.shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨start, Nat.le_refl _, startBound, startAligned, by rw [globalsEq]; exact heap, earlier⟩
  · have strideAligned := (stride_bounds kind).2.2
    have usedAligned := (rounded_bounds (2 * old.capacity)).2.2
    refine ⟨relocatedEnd kind start (2 * old.capacity), ?_, valid.upper .position, ?_, ?_, ?_⟩
    · dsimp only [relocatedEnd]; omega
    · simp [relocatedEnd, Nat.add_mod, Nat.mul_mod, startAligned, strideAligned, usedAligned]
    · rw [globalsEq]
      simp [HolFiniteMapExact.update, FUPDATE]
    · intro pool
      by_cases isHeader : pool = .header
      · subst pool
        have before := earlier .header
        change old.base .header + 72 ≤ start at before
        change old.base .header + 72 ≤ relocatedEnd kind start (2 * old.capacity)
        dsimp only [relocatedEnd]
        omega
      · exact (relocated_array_bounds kind (old.base .header) start (2 * old.capacity) pool isHeader).2

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.header_pointer
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.cursor

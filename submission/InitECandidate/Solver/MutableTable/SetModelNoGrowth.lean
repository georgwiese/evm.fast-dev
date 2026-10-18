import InitECandidate.Solver.MutableTable.SetModelCursor

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Spare half-capacity room rules out growth in the actual original
setter. Both the layout and every global, including the heap, are retained. -/
theorem ModelPost.no_growth {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old plan : Plan}
    {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}
    (post : ModelPost source kind old start count paid globals memory target plan slots)
    (positive : 0 < old.capacity) (room : 2 * count + 2 ≤ old.capacity) : plan = old ∧ globals = source.globals := by
  have same : plan = old := by
    by_contra different
    have threshold := post.grew different
    omega
  refine ⟨same, ?_⟩
  rcases post.shape with ⟨_, globals⟩ | ⟨relocated, _⟩
  · exact globals
  · have capacity := congrArg Plan.capacity (same.symm.trans relocated)
    change old.capacity = 2 * old.capacity at capacity
    omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.no_growth

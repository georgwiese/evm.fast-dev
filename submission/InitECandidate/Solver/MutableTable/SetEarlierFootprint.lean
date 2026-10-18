import InitECandidate.Solver.MutableTable.SetModelSeparation

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- A protected old word below the live cursor remains outside the setter's
new pools. This handles objects between old pools, such as the fixed journal,
as well as objects preceding all pools. -/
theorem ModelPost.outside_earlier {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old plan : Plan}
    {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}
    (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind plan) (address : BitVec 64) (before : address.toNat < start)
    (outside : TableFootprint.Outside kind old address) : TableFootprint.Outside kind plan address := by
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact outside
  · intro pool offset inside equal
    by_cases header : pool = .header
    · subst pool
      exact outside .header offset inside equal
    · have numeric := congrArg BitVec.toNat equal
      rw [number kind _ valid pool offset inside] at numeric
      have after : start ≤ (relocated kind (old.base .header) start (2 * old.capacity)).base pool := by
        cases pool with
        | header => exact (header rfl).elim
        | keys => exact Nat.le_refl _
        | values => simp only [relocated]; omega
        | used => simp only [relocated]; omega
        | order => simp only [relocated]; omega
        | position => simp only [relocated]; omega
      omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.outside_earlier

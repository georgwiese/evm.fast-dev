import InitECandidate.Solver.MutableTable.SetModelOwnership
import InitECandidate.Solver.MutableTable.GrowRuntime.Amortized

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

variable {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old plan : Plan}
  {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}

/-- Apply the amortized growth price directly to the actual full-setter
postcondition and the two caller bounds exported by model_call. -/
theorem ModelPost.amortized (post : ModelPost source kind old start count paid globals memory target plan slots)
    (minimum : 4 ≤ old.capacity) (even : old.capacity % 2 = 0) (half : 2 * count ≤ old.capacity)
    (bounded : paid ≤ modelPrice kind old.capacity count + 1)
    (unchanged : plan = old → paid ≤ noGrowthPrice kind count + 1) :
    paid + GrowRuntime.growthPotential kind old.capacity ≤ noGrowthPrice kind count + 1 + GrowRuntime.growthPotential kind plan.capacity := by
  by_cases same : plan = old
  · have linear := unchanged same
    rw [same]
    omega
  · have capacity : plan.capacity = 2 * old.capacity := by
      rcases post.shape with ⟨equal, _⟩ | ⟨rfl, _⟩
      · exact (same equal).elim
      · rfl
    have growth := GrowRuntime.growth_paid_by_capacity kind old.capacity count minimum even half
    have priced := model_caller_decompose kind old.capacity count
    rw [capacity]
    omega

theorem ModelPost.amortized_power (post : ModelPost source kind old start count paid globals memory target plan slots)
    (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits) (half : 2 * count ≤ old.capacity)
    (bounded : paid ≤ modelPrice kind old.capacity count + 1)
    (unchanged : plan = old → paid ≤ noGrowthPrice kind count + 1) :
    paid + GrowRuntime.growthPotential kind old.capacity ≤ noGrowthPrice kind count + 1 + GrowRuntime.growthPotential kind plan.capacity := by
  have shape := GrowRuntime.capacity_shape old.capacity bits power minimum
  exact post.amortized shape.1 shape.2 half bounded unchanged

/-- The capacity high-water bound uses actual observed populations even
when later deletion reduces the current item count. -/
theorem ModelPost.capacity_high_water (post : ModelPost source kind old start count paid globals memory target plan slots) :
    plan.capacity ≤ max old.capacity (4 * (slots.length + 1)) := by
  by_cases same : plan = old
  · rw [same]
    exact Nat.le_max_left _ _
  · exact (Nat.le_of_lt (post.growth_count_bound same)).trans (Nat.le_max_right _ _)

def cumulative (amount : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cumulative amount n + amount n

/-- Telescope the actual per-setter inequality. Event counts and physical
table lifetimes still have to be supplied by original caller execution. -/
theorem cumulative_amortized (kind : KeyHash.Kind) (capacity paid base : Nat → Nat) (count : Nat)
    (localBounds : ∀ index < count, paid index + GrowRuntime.growthPotential kind (capacity index) ≤
      base index + GrowRuntime.growthPotential kind (capacity (index + 1))) :
    cumulative paid count + GrowRuntime.growthPotential kind (capacity 0) ≤
      cumulative base count + GrowRuntime.growthPotential kind (capacity count) := by
  induction count with
  | zero => simp only [cumulative, Nat.zero_add, le_refl]
  | succ count ih =>
    have prior := ih (by intro index inside; exact localBounds index (by omega))
    have last := localBounds count (by omega)
    simp only [cumulative]
    omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.amortized
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.amortized_power
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.capacity_high_water
#print axioms InitECandidate.Solver.MutableTable.Set.cumulative_amortized

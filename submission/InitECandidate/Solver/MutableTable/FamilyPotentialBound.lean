import InitECandidate.Solver.MutableTable.FamilyPacking
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact
open scoped BigOperators

theorem Model.population_bound {ι : Type} [Fintype ι] {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (index : ι) : (objects index).slots.length ≤ 268435456 := by
  classical
  have total := family.capacity_sum
  have individual : (objects index).plan.capacity ≤ ∑ other, (objects other).plan.capacity :=
    Finset.single_le_sum (f := fun other : ι => (objects other).plan.capacity) (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  obtain ⟨bits, power, minimum⟩ := (family.tables index).power
  have bitsSmall : bits ≤ 29 := by
    by_contra large
    have more := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 30 ≤ bits by omega)
    rw [← power] at more
    change 1073741824 ≤ (objects index).plan.capacity at more
    omega
  have capacity := Nat.pow_le_pow_right (by decide : 1 ≤ 2) bitsSmall
  rw [← power] at capacity
  change (objects index).plan.capacity ≤ 536870912 at capacity
  have half := (family.tables index).half
  omega

theorem object_potential_upper (object : Object) :
    24 * object.potential ≤ object.plan.capacity * object.plan.capacity + 360 * object.plan.capacity := by
  let capacity := object.plan.capacity
  have triUpper : 2 * WitnessBuild.triangle (capacity / 2) ≤ (capacity / 2) * (capacity / 2) := by
    rw [WitnessBuild.triangle_double]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have divided : 2 * (capacity / 2) ≤ capacity := by omega
  have squares := Nat.mul_le_mul divided divided
  have triBound : 8 * WitnessBuild.triangle (capacity / 2) ≤ capacity * capacity := by nlinarith
  have third : 3 * (WitnessBuild.triangle (capacity / 2) / 3) ≤ WitnessBuild.triangle (capacity / 2) := by omega
  have slope : GrowRuntime.growthSlope object.kind ≤ 15 := by cases object.kind <;> decide
  have slopeBound := Nat.mul_le_mul_right capacity slope
  change 24 * (WitnessBuild.triangle (capacity / 2) / 3 + GrowRuntime.growthSlope object.kind * capacity) ≤ capacity * capacity + 360 * capacity
  nlinarith

theorem potential_capacity {ι : Type} [Fintype ι] (objects : ι → Object) :
    24 * potential objects ≤ (∑ index, (objects index).plan.capacity) * (∑ index, (objects index).plan.capacity) +
      360 * (∑ index, (objects index).plan.capacity) := by
  classical
  have squareSum (indices : Finset ι) :
      (∑ index ∈ indices, (objects index).plan.capacity * (objects index).plan.capacity) ≤
        (∑ index ∈ indices, (objects index).plan.capacity) * (∑ index ∈ indices, (objects index).plan.capacity) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index rest absent ih =>
      simp only [Finset.sum_insert absent]
      simp only [Nat.add_mul, Nat.mul_add]
      omega
  have individual := Finset.sum_le_sum (s := Finset.univ) (fun index _ => object_potential_upper (objects index))
  have left : (∑ index, 24 * (objects index).potential) = 24 * potential objects := by rw [potential, Finset.mul_sum]
  have right : (∑ index, ((objects index).plan.capacity * (objects index).plan.capacity + 360 * (objects index).plan.capacity)) =
      (∑ index, (objects index).plan.capacity * (objects index).plan.capacity) + 360 * (∑ index, (objects index).plan.capacity) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [left, right] at individual
  have bounded := squareSum Finset.univ
  exact Nat.le_trans individual (Nat.add_le_add_right bounded _)

/-- A single concrete cap for the entire current family's amortization
potential, derived from physical ownership alone, independently of a chosen
event count or favorable hashes. This is a local resource term, not K. -/
theorem Model.potential_bound {ι : Type} [Fintype ι] {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) : potential objects ≤ 17497087144886042 := by
  have slots := family.capacity_sum
  have square := Nat.mul_le_mul slots slots
  have linear := Nat.mul_le_mul_left 360 slots
  have bound := potential_capacity objects
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.object_potential_upper
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.population_bound
#print axioms InitECandidate.Solver.MutableTable.TableFamily.potential_capacity
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.potential_bound

import InitECandidate.Solver.MutableTable.FamilyPotential
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact NaturalLayout
open scoped BigOperators

private def packedPool (pool : Fin 4) : Pool :=
  if pool.val = 0 then .keys else if pool.val = 1 then .values else if pool.val = 2 then .order else .position
private def packedWeight (pool : Fin 4) : Nat := if pool.val = 0 then 3 else 1

private theorem packedPool_injective : Function.Injective packedPool := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [packedPool]

private theorem packed_span (object : Object) (pool : Fin 4) :
    8 * (packedWeight pool * object.plan.capacity) ≤ size object.kind object.plan (packedPool pool) := by
  have strideMin : 24 ≤ stride object.kind := by cases object.kind <;> decide
  have keyRoom := Nat.mul_le_mul_right object.plan.capacity strideMin
  fin_cases pool <;> simp [packedPool, packedWeight, size]
  all_goals omega

private abbrev Packed {ι : Type} (objects : ι → Object) :=
  Σ index : ι, Σ pool : Fin 4, Fin (packedWeight pool * (objects index).plan.capacity)

private def packedNumber {ι : Type} (objects : ι → Object) (word : Packed objects) : Nat :=
  (objects word.1).plan.base (packedPool word.2.1) / 8 + word.2.2.val

private theorem packed_interval {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (word : Packed objects) :
    (objects word.1).plan.base (packedPool word.2.1) ≤ 8 * packedNumber objects word ∧
      8 * packedNumber objects word < (objects word.1).plan.base (packedPool word.2.1) + size (objects word.1).kind (objects word.1).plan (packedPool word.2.1) := by
  have aligned := (family.tables word.1).valid.aligned (packedPool word.2.1)
  have span := packed_span (objects word.1) word.2.1
  have inside := word.2.2.isLt
  unfold packedNumber
  omega

private theorem packed_bounds {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (word : Packed objects) :
    337641472 ≤ packedNumber objects word ∧ packedNumber objects word < 4225761187 := by
  have interval := packed_interval family word
  have lower := (family.tables word.1).valid.lower (packedPool word.2.1)
  have upper := (family.tables word.1).valid.upper (packedPool word.2.1)
  omega

private theorem packedNumber_injective {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) : Function.Injective (packedNumber objects) := by
  intro first second same
  have firstInterval := packed_interval family first
  have secondInterval := packed_interval family second
  rcases first with ⟨first, left, leftOffset⟩
  rcases second with ⟨second, right, rightOffset⟩
  dsimp only at firstInterval secondInterval
  have indices : first = second := by
    by_contra different
    rcases family.apart first second different (packedPool left) (packedPool right) with before | afterPool <;> omega
  subst second
  have pools : left = right := by
    by_contra different
    have separate := (family.tables first).valid.disjoint (packedPool left) (packedPool right) (fun equal => different (packedPool_injective equal))
    rcases separate with before | afterPool <;> omega
  subst right
  have offsets : leftOffset = rightOffset := by
    apply Fin.ext
    change (objects first).plan.base (packedPool left) / 8 + leftOffset.val =
      (objects first).plan.base (packedPool left) / 8 + rightOffset.val at same
    omega
  cases offsets
  rfl

private def packedInto {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (word : Packed objects) : Fin 3888119715 :=
  ⟨packedNumber objects word - 337641472, by have bounded := packed_bounds family word; omega⟩

/-- Six words per slot fit in four actually owned pools: three key words,
one value, one order and one position. Their physical addresses are distinct
across the whole family, so total capacity is bounded by the real heap range.
Headers and used arrays can only make this conservative bound smaller. -/
theorem Model.capacity_sum {ι : Type} [Fintype ι] {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) : (∑ index, (objects index).plan.capacity) ≤ 648019952 := by
  classical
  have injective : Function.Injective (packedInto family) := by
    intro first second same
    have numbers := congrArg Fin.val same
    change packedNumber objects first - 337641472 = packedNumber objects second - 337641472 at numbers
    have firstBound := packed_bounds family first
    have secondBound := packed_bounds family second
    apply packedNumber_injective family
    omega
  have cards := Fintype.card_le_of_injective (packedInto family) injective
  change Fintype.card (Σ index : ι, Σ pool : Fin 4, Fin (packedWeight pool * (objects index).plan.capacity)) ≤ Fintype.card (Fin 3888119715) at cards
  simp only [Fintype.card_sigma, Fintype.card_fin] at cards
  have per (capacity : Nat) : (∑ pool : Fin 4, packedWeight pool * capacity) = 6 * capacity := by
    simp [Fin.sum_univ_succ, packedWeight]
    omega
  simp only [per] at cards
  rw [← Finset.mul_sum] at cards
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.capacity_sum

import InitECandidate.Solver.GasBudget.JournalCounterLedger
import InitECandidate.Solver.GasBudget.JournalLoop
import InitECandidate.Solver.MutableTable.FamilyPotentialBound

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact MutableTable

theorem triangle_add (first second : Nat) :
    WitnessBuild.triangle (first + second) = WitnessBuild.triangle first + WitnessBuild.triangle second + first * second := by
  induction second with
  | zero => simp [WitnessBuild.triangle]
  | succ second ih =>
    change WitnessBuild.triangle (first + second) + (first + second) =
      WitnessBuild.triangle first + (WitnessBuild.triangle second + second) + first * (second + 1)
    rw [ih, Nat.mul_succ]
    omega

theorem price_combine (population first second : Nat) :
    price population first + price population second ≤ price population (first + second) := by
  simp only [price, triangle_add, Nat.mul_add]
  omega

theorem price_mono_count (population small large : Nat) (bounded : small ≤ large) : price population small ≤ price population large := by
  have linear := Nat.mul_le_mul_left (38 * population + 40) bounded
  have quadratic := Nat.mul_le_mul_left 38 (GrowRuntime.triangle_mono small large bounded)
  exact Nat.add_le_add linear quadratic

theorem price_sum (population : Nat) (counts : List Nat) :
    (counts.map (price population)).sum ≤ price population counts.sum := by
  induction counts with
  | nil => simp [price, WitnessBuild.triangle]
  | cons head counts ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (price_combine population head counts.sum)

/-- An accounted journal prefix pays the quadratic term once on its total
restores, bounded by actual appends plus initially live entries. The program
must still construct the ledger and identify the real per-call counts. -/
theorem accounted_price {initial : Nat} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ledger : CounterLedger initial source) (population : Nat) (counts : List Nat) (actual : counts.sum = ledger.restored) :
    counts.length + (counts.map (price population)).sum ≤ counts.length + price population (initial + ledger.appended) := by
  have combined := price_sum population counts
  have bounded := price_mono_count population ledger.restored (initial + ledger.appended) ledger.restored_le
  rw [actual] at combined
  omega

/-- Close a cumulative amortized inequality using the actual final physical
family's potential, rather than assuming a final-capacity or growth budget.
The source work and whole-execution ledger still have to be supplied. -/
theorem close_accounted_price {ι : Type} [Fintype ι] {initial : Nat}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → TableFamily.Object}
    (family : TableFamily.Model source cursor objects) (ledger : CounterLedger initial source)
    (paid other initialPotential population : Nat)
    (amortized : paid + initialPotential ≤ other + price population ledger.restored + TableFamily.potential objects) :
    paid ≤ other + price population (initial + ledger.appended) + 17497087144886042 := by
  have potential := family.potential_bound
  have bounded := price_mono_count population ledger.restored (initial + ledger.appended) ledger.restored_le
  omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.triangle_add
#print axioms InitECandidate.Solver.GasBudget.Journal.price_combine
#print axioms InitECandidate.Solver.GasBudget.Journal.price_mono_count
#print axioms InitECandidate.Solver.GasBudget.Journal.price_sum
#print axioms InitECandidate.Solver.GasBudget.Journal.accounted_price
#print axioms InitECandidate.Solver.GasBudget.Journal.close_accounted_price

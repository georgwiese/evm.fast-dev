import InitECandidate.Solver.GasBudget.JournalProgram
import InitECandidate.Solver.MutableTable.WitnessBuildBudget

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def OtherGlobals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∀ key : MlS, key ≠ ofString "heap_ptr" → key ≠ ofString "journal_n" → target.globals.lookup key = source.globals.lookup key

theorem OtherGlobals.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) : OtherGlobals source source := by
  intro key heap counter
  rfl

theorem OtherGlobals.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : OtherGlobals source middle) (second : OtherGlobals middle target) : OtherGlobals source target := by
  intro key heap counter
  exact (second key heap counter).trans (first key heap counter)

def price (population remaining : Nat) : Nat :=
  (38 * population + 40) * remaining + 38 * WitnessBuild.triangle remaining

theorem price_step (population remaining : Nat) :
    price population (remaining + 1) = 38 * population + 40 + price (population + 1) remaining := by
  simp only [price, WitnessBuild.triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.OtherGlobals.trans
#print axioms InitECandidate.Solver.GasBudget.Journal.price_step

import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

theorem Result.relax {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor nextCursor cutoff protectedCursor base cap count nextCount price appendLimit populationLimit : Nat}
    {objects next : ι → TableFamily.Object} {outer : ι} {nextEntries : Nat → Journal.Entry ι}
    {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop}
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit)
    (otherPrice otherAppends otherPopulation : Nat)
    (priceBound : price ≤ otherPrice) (appendBound : appendLimit ≤ otherAppends) (populationBound : populationLimit ≤ otherPopulation) :
    Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty otherPrice otherAppends otherPopulation := by
  exact {result with
    work := Nat.le_trans result.work (Nat.add_le_add_right priceBound _)
    appends := Nat.le_trans result.appends appendBound
    populations := fun index => Nat.le_trans (result.populations index) populationBound }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.relax

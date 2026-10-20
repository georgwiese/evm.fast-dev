import InitECandidate.Solver.Mpt.AccountMutationComposition

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

theorem Result.local_agreement {ι : Type} [Fintype ι]
    {source finish post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor nextCursor cutoff protectedCursor base cap count nextCount price appendLimit populationLimit : Nat}
    {objects next : ι → TableFamily.Object} {outer : ι} {nextEntries : Nat → Journal.Entry ι}
    {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop}
    (result : Result source finish cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit)
    (agreement : emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish) :
    Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit := by
  have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := post.locals}) agreement
  change post = {finish with locals := post.locals} at same
  rw [same]
  exact result.locals post.locals

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.local_agreement

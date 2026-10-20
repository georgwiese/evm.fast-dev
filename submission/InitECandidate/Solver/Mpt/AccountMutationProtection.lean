import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

theorem Result.restrict_protection {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor nextCursor cutoff protectedCursor : Nat}
    {objects next : ι → TableFamily.Object} {outer : ι} {base cap count nextCount : Nat} {entries : Nat → Journal.Entry ι}
    {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop} {price appends population : Nat}
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount entries accounts nextAccounts property nextProperty price appends population)
    (boundary : Nat) (before : boundary ≤ protectedCursor) :
    Result source post cursor nextCursor cutoff boundary objects next outer base cap count nextCount entries accounts nextAccounts property nextProperty price appends population :=
  {result with protectedBefore := Nat.le_trans before result.protectedBefore
               frame := fun query above earlier outside away => result.frame query above (Nat.lt_of_lt_of_le earlier before) outside away}

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.restrict_protection

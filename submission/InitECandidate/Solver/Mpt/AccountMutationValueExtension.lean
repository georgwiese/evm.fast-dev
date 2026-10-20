import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

/-- A freshly constructed non-account payload can be published without
weakening any account-cache or outer-storage ownership obligation. -/
theorem Result.add_non_account_value {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor nextCursor cutoff protectedCursor : Nat}
    {objects next : ι → TableFamily.Object} {outer : ι} {base cap count nextCount : Nat} {entries : Nat → Journal.Entry ι}
    {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop} {price appends population : Nat}
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount entries accounts nextAccounts property nextProperty price appends population)
    (writer : ι) (nonAccount : (objects writer).kind ≠ .account) (different : writer ≠ outer) (fresh : BitVec 64) :
    Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount entries accounts nextAccounts property (AccountValueExtension.added nextProperty writer fresh) price appends population := by
  refine {result with
    values := AccountValueExtension.live_values post next nextProperty result.values writer fresh
    savedValues := AccountValueExtension.saved_values entries nextCount nextProperty result.savedValues writer fresh
    propertyIncluded := fun index value owned => Or.inl (result.propertyIncluded index value owned)
    outerValues := fun value => (AccountValueExtension.other nextProperty writer outer fresh value different.symm).trans (result.outerValues value)
    readerKnown := ?_ }
  intro index kind known value owned
  rcases owned with old | ⟨rfl,_⟩
  · exact result.readerKnown index kind known value old
  · exact False.elim (nonAccount kind)

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.add_non_account_value

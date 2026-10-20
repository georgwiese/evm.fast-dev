import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

/-- Preserve the branch-sensitive cost of a checked single account update
while exposing its actual journal/ownership endpoint for composition. -/
theorem of_balance {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor cutoff protectedCursor population base cap count : Nat}
    {objects : ι → TableFamily.Object} {writer outer : ι} {accounts : List (BitVec 64)}
    {property : ι → BitVec 64 → Prop} {budget : Bool → Bool → Nat → Nat}
    (oracle : post.ffi.oracle = source.ffi.oracle)
    (different : writer ≠ outer)
    (protectedBefore : protectedCursor ≤ cursor)
    (result : AccountBalanceSet.Result source post cursor cutoff population objects writer base cap count accounts property budget) :
    ∃ (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object)
      (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      iterations ≤ population ∧ Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (budget destroyed found iterations) 3 (population + iterations + 2) := by
  obtain ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,price,codes,
    environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember,populations⟩ := result
  have spent : source.clock - post.clock = paid := by rw [clock]; omega
  have delta : count + added - count = added := by omega
  refine ⟨destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,AccountValueExtension.added property writer (BitVec.ofNat 64 freshCursor),count + added,visits,?_⟩
  refine {
    clockForward := by omega
    cursorForward := forward
    protectedBefore := protectedBefore
    countForward := by omega
    countBound := capacityBound
    appends := by omega
    family := models
    image := image
    zone := zone
    work := by rw [spent]; exact price
    populations := populations
    code := codes
    oracle := oracle
    environment := environment
    globals := globals
    values := values
    savedValues := saved
    registry := registry
    extension := extension
    effect := by rw [delta]; exact effect
    metadata := metadata
    frame := fun query above before outside away => frame query above (Nat.lt_of_lt_of_le before protectedBefore) outside away
    counter := counter
    propertyIncluded := fun _ _ owned => Or.inl owned
    outerValues := fun value => AccountValueExtension.other property writer outer _ value different.symm
    readerKnown := ?_ }
  intro index _ known value owned
  rcases owned with old | ⟨_,rfl⟩
  · exact extension.known value (known value old)
  · exact Or.inr freshMember

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.of_balance

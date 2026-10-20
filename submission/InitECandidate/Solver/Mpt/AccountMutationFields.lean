import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

variable {ι : Type} [Fintype ι]
variable {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {cursor nextCursor cutoff protectedCursor base cap count nextCount price appendLimit populationLimit : Nat}
variable {objects next : ι → TableFamily.Object} {outer : ι} {nextEntries : Nat → Journal.Entry ι}
variable {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop}

theorem Result.header_cell
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit)
    (environment : WarmKeys.Environment source) (query : BitVec 64) (index : ι)
    (mapped : source.memaddrs query) (stored : source.memory query = .word (objects index).pointer)
    (above : cutoff ≤ query.toNat) (before : query.toNat < protectedCursor)
    (outside : TableFamily.Outside objects query) (away : Journal.Away base cap query) :
    post.memaddrs query ∧ post.memory query = .word (next index).pointer ∧ TableFamily.Outside next query := by
  have changed := result.frame query above before outside away
  refine ⟨?_,?_,changed.1⟩
  · rw [result.environment.domain,← environment.domain]
    exact mapped
  · rw [result.metadata.pointers index]
    exact changed.2.trans stored

theorem Result.references
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit)
    (references : ∀ value,property outer value → ∃ index,(objects index).pointer = value ∧ (objects index).kind = .word) :
    ∀ value,nextProperty outer value → ∃ index,(next index).pointer = value ∧ (next index).kind = .word := by
  intro value owned
  obtain ⟨index,pointer,kind⟩ := references value ((result.outerValues value).mp owned)
  exact ⟨index,(result.metadata.pointers index).trans pointer,(result.metadata.kinds index).trans kind⟩

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.header_cell
#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.references

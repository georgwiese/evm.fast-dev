import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.Mpt.StateWorldFrame
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

/-- The protected boundary is independent of the moving allocation cursor:
updates may change a freshly copied account while retaining the witness and
all older fixed state headers needed by subsequent lookups. -/
theorem Result.immutable_context {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor nextCursor cutoff protectedCursor base cap count nextCount price appendLimit populationLimit : Nat}
    {objects next : ι → TableFamily.Object} {outer : ι} {nextEntries : Nat → Journal.Entry ι}
    {accounts nextAccounts : List (BitVec 64)} {property nextProperty : ι → BitVec 64 → Prop}
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty price appendLimit populationLimit)
    (ws root nibs stp pad scratchPtr limit : BitVec 64) (frozenEnd valueLimit : Nat)
    (family : TableFamily.Model source cursor objects)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (protectedWorld : frozenEnd ≤ protectedCursor) (floors : ∀ index,frozenEnd ≤ (objects index).floor) (journalAfter : frozenEnd ≤ base)
    (hash : Keccak256.Environment source stp pad) (arena : Rlp.Validation.Arena source scratchPtr limit) :
    Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment post stp pad ∧ Rlp.Validation.Arena post scratchPtr limit ∧
      frozenEnd ≤ nextCursor ∧ (∀ index,frozenEnd ≤ (next index).floor) := by
  have domain : post.memaddrs = source.memaddrs := result.environment.domain.trans world.domain.symm
  have endian : post.be = source.be := result.environment.little.trans world.little.symm
  have nextWorld : WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit := by
    apply WsAccountLeaf.World.of_agreement source post ws root nibs cutoff frozenEnd valueLimit world domain endian
      (result.globals _ (by decide) (by decide)) (result.globals _ (by decide) (by decide))
    intro query needed
    have bounds := world.footprint query needed
    have outside : TableFamily.Outside objects query := by
      intro index
      exact TableFamily.outside_floor source (objects index).kind (objects index).plan (objects index).slots cursor (objects index).floor (family.tables index) query
        (Nat.lt_of_lt_of_le bounds.2 (floors index))
    exact (result.frame query bounds.1 (Nat.lt_of_lt_of_le bounds.2 protectedWorld) outside (Or.inl (by omega))).2
  refine ⟨⟨nextWorld⟩,StateWorldFrame.hash_environment source post stp pad hash domain result.code result.oracle result.globals,
    StateWorldFrame.scratch_arena source post scratchPtr limit arena domain result.globals,?_,?_⟩
  · exact Nat.le_trans protectedWorld (Nat.le_trans result.protectedBefore result.cursorForward)
  · intro index
    rw [result.metadata.floors index]
    exact floors index

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.immutable_context

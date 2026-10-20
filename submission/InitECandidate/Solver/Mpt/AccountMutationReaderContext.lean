import InitECandidate.Solver.Mpt.AccountBalanceSetResult
import InitECandidate.Solver.Mpt.StateWorldFrame
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

/-- The real mutation result retains the immutable provider context and
registered cache values needed by a subsequent account lookup. -/
theorem Result.reader_context {ι : Type} [Fintype ι]
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor cutoff population base cap count : Nat} {objects : ι → TableFamily.Object} {accountWriter : ι}
    {accounts : List (BitVec 64)} {property : ι → BitVec 64 → Prop} {budget : Bool → Bool → Nat → Nat}
    (result : Result source post cursor cutoff population objects accountWriter base cap count accounts property budget)
    (ws root nibs stp pad scratchPtr limit : BitVec 64) (frozenEnd valueLimit : Nat)
    (family : TableFamily.Model source cursor objects)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (afterWorld : frozenEnd ≤ cursor) (floors : ∀ index,frozenEnd ≤ (objects index).floor) (journalAfter : frozenEnd ≤ base)
    (hash : Keccak256.Environment source stp pad) (arena : Rlp.Validation.Arena source scratchPtr limit)
    (program : ProgHOL 64) (answer : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source program = (answer,post)) :
    ∃ (nextCursor : Nat) (next : ι → TableFamily.Object) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop),
      cursor ≤ nextCursor ∧ TableFamily.Model post nextCursor next ∧ AccountDecode.Registry post cutoff nextCursor next nextAccounts ∧
      AccountDecode.Registry.Extension accounts nextAccounts cursor ∧ TableFamily.ValuesHave post next nextProperty ∧
      Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment post stp pad ∧ Rlp.Validation.Arena post scratchPtr limit ∧
      (∀ index,frozenEnd ≤ (next index).floor) ∧
      (∀ index,(∀ value,property index value → AccountDecode.Registry.Known accounts value) →
        ∀ value,nextProperty index value → AccountDecode.Registry.Known nextAccounts value) := by
  obtain ⟨freshCursor,paid,nextCursor,next,nextEntries,nextAccounts,added,destroyed,found,iterations,freshForward,extension,funded,clock,forward,addedPositive,addedBound,capacityBound,models,image,zone,price,codes,
    environment,globals,values,saved,registry,effect,metadata,frame,counter,appends,visits,freshMember⟩ := result
  have domain : post.memaddrs = source.memaddrs := environment.domain.trans world.domain.symm
  have endian : post.be = source.be := environment.little.trans world.little.symm
  have oracle := Input.evaluation_oracle source post program answer run
  have nextWorld := StateWorldFrame.witness_world source post ws root nibs cutoff frozenEnd valueLimit cursor base cap objects next world family afterWorld floors journalAfter domain endian globals frame
  have nextHash := StateWorldFrame.hash_environment source post stp pad hash domain codes oracle globals
  have nextArena := StateWorldFrame.scratch_arena source post scratchPtr limit arena domain globals
  refine ⟨nextCursor,next,nextAccounts,AccountValueExtension.added property accountWriter (BitVec.ofNat 64 freshCursor),forward,models,registry,extension,values,nextWorld,nextHash,nextArena,?_,?_⟩
  · intro index
    rw [metadata.floors index]
    exact floors index
  · intro index known value owned
    rcases owned with old | ⟨_,rfl⟩
    · exact extension.known value (known value old)
    · exact Or.inr freshMember

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.Result.reader_context

import InitECandidate.Solver.Mpt.WitnessCoreResultNode
import InitECandidate.Solver.Mpt.WitnessCoreResolveState
import InitECandidate.Solver.Input.WitnessResolveResult

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem ResultOwned.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper node) (memory : target.memory=source.memory) :
    ResultOwned target lower upper node := by
  rcases owned with zero|allocated
  · exact Or.inl zero
  · obtain ⟨tag,tagCell,tagBound⟩:=allocated.kind
    exact Or.inr ⟨allocated.arena,allocated.aligned,allocated.fresh,allocated.before,tag,by rw [memory]; exact tagCell,tagBound⟩

theorem ResultOwned.weaken (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (lower upper smaller larger : Nat) (owned : ResultOwned source lower upper node) (first : smaller≤lower) (last : upper≤larger) :
    ResultOwned source smaller larger node := by
  rcases owned with zero|allocated
  · exact Or.inl zero
  · exact Or.inr (allocated.weaken source node lower upper smaller larger first last)

/-- A real scratch-record write below the result's allocation frontier
cannot change its constructor tag or physical header ownership. -/
theorem ResultOwned.store_below (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node address word : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper node) (below : address.toNat<lower) :
    ResultOwned {source with memory:=StoreWord.put source.memory address word} lower upper node := by
  rcases owned with zero|allocated
  · exact Or.inl zero
  · have away : node≠address:=by intro same; have number:=congrArg BitVec.toNat same; have fresh:=allocated.fresh; omega
    obtain ⟨tag,tagCell,tagBound⟩:=allocated.kind
    exact Or.inr ⟨allocated.arena,allocated.aligned,allocated.fresh,allocated.before,tag,(if_neg away).trans tagCell,tagBound⟩

/-- The genuine original resolver's terminal result is null or its
fresh32-byte hashed node. Both its actual header and next heap extent
come from the same complete returned-result contract. -/
theorem resolve_result_owned (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap next node : BitVec 64) (aligned : heap.toNat%8=0)
    (result : Input.Main.RunAttemptConstructors.ResolveResult post db heap (resolveAnswer 0#64 node 0#64 0#64))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next))) :
    ResultOwned post heap.toNat next.toNat node := by
  rcases result with empty|⟨valueEq,arena,tag,hashData,finalHeap,actualCell,finalArena,finalAligned,before⟩|
      ⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan⟩
  · have zero : node=0#64:=by simpa [resolveAnswer] using empty
    exact Or.inl zero
  · have same : node=heap:=by simpa [resolveAnswer] using valueEq
    subst node
    have finalEq : finalHeap=next:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst finalHeap
    exact Or.inr (ResultNode.of_region post heap 0#64 32 heap.toNat next.toNat arena (Nat.le_refl _) aligned (Nat.le_refl _) before tag (by decide))
  · simp [resolveAnswer] at valueEq

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultOwned.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultOwned.weaken
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultOwned.store_below
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_result_owned

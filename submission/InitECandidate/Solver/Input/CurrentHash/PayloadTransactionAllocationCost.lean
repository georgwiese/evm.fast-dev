import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionSuffixCost
import InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

def transactionTailPrice (input : Guest.InputBlob) (length start size : Nat) :=
  5*transactionBytes input start size+3391*VarList.decodedCount input start size+848*withdrawalCount input+5*balanceLength input length+14667

theorem State.transaction_i_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size)) (rootsAligned : roots.toNat%8=0)
    (rootsAfter : ch.toNat≤roots.toNat) (rootsBefore : roots.toNat+32*VarList.decodedCount input start size≤cursor.toNat)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterTxRoots=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size := by
  rw [transaction_shapes.2.2.2.2.1] at actual
  apply ClockCost.declared_terminating source post "i" (.const 0#64) 0#64 transactionLoopAndSuffix (transactionTailPrice input length start size) rfl _ result actual notTimeout
  intro observed target evaluated noTimeout
  have next := data.bound "i" 0#64 (by decide)
  have nextSaved : SavedCursor (bind source "i" 0#64) "m2" ch base := saved.of_lookup ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved.binding)
  have round := next.transaction_round roots 0 ((bind_lookup_other source "i" "txs" 0#64 (by decide)).trans pointer)
    ((bind_lookup_other source "i" "ntx" 0#64 (by decide)).trans count) ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans root) (bind_lookup_same _ _ _)
  have geometry := next.transaction_geometry roots rootsArena rootsAligned rootsAfter rootsBefore
  have paid := next.transaction_loop_suffix_cost (post:=target) nextSaved roots 0 round (by omega) geometry rootsAfter observed evaluated noTimeout
  simp only [Transactions.allowance,VarList.sumPrefix,Nat.sub_zero] at paid
  change source.clock-target.clock≤5*transactionBytes input start size+3303*VarList.decodedCount input start size+
    (88*VarList.decodedCount input start size+848*withdrawalCount input+5*balanceLength input length+14667) at paid
  have arithmetic : ∀ bytes n wd bal : Nat,5*bytes+3303*n+(88*n+848*wd+5*bal+14667)≤5*bytes+3391*n+848*wd+5*bal+14667 := by intro bytes n wd bal; omega
  exact Nat.le_trans paid (arithmetic _ _ _ _)

/-- Same actual scoped transaction-root allocation: failed guards are priced;
its real normal return supplies the root arena and next bounded frontier. -/
theorem State.transaction_after_second_mark_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterSecondMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+2 := by
  have bounded := data.transaction_data.2.2
  let amount := BitVec.ofNat 64 (32*VarList.decodedCount input start size+32)
  have number : amount.toNat=32*VarList.decodedCount input start size+32 := roots_amount_number _ bounded
  rw [transaction_shapes.2.2.2.1] at actual
  exact AllocationScopeCost.cost source post cursor amount data.context.installed data.context.heap data.context.heapBound "roots" (rootsAllocationArguments "ntx") afterTxRoots
    (transactionTailPrice input length start size) (roots_arguments_read source "ntx" _ count)
    (by intro target room same observed final evaluated noTimeout
        let entry := CallNormal.continuationEntry source target "roots" (.val (.word cursor))
        have next := data.allocated amount room same
        have kept (name : String) (different : ofString "roots"≠ofString name) := CallNormal.continuation_lookup_other source target "roots" name (.val (.word cursor)) different
        have nextSaved : SavedCursor entry "m2" ch base := saved.of_lookup ((kept "m2" (by decide)).trans saved.binding)
        have rootsArena : AllocatedBytes.Arena cursor (32*VarList.decodedCount input start size) := ⟨data.context.heapLower,by rw [number] at room; omega⟩
        have guards := PersistentAlloc.guards cursor amount room
        have paid := next.transaction_i_cost (post:=final) nextSaved cursor ((kept "txs" (by decide)).trans pointer) ((kept "ntx" (by decide)).trans count)
          (CallNormal.continuation_lookup_same _ _ _ _) rootsArena data.context.aligned (by have h:=data.afterChunks; omega)
          (by have h:=guards.2.2.1; rw [number] at h; omega) observed evaluated noTimeout
        exact paid)
    result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_i_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_after_second_mark_cost

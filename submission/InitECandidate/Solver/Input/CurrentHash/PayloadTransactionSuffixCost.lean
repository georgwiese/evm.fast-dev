import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionState
import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalScopeCost

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

def transactionBytes (input : Guest.InputBlob) (start size : Nat) := VarList.sumPrefix (Transactions.decodedLengths input start size) (VarList.decodedCount input start size)

theorem State.after_transaction_list_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterTransactionList=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤848*withdrawalCount input+5*balanceLength input length+11498 := by
  rw [transaction_shapes.2.2.2.2.2.2.2] at actual
  have paid := ClockCost.sequence_terminating source post _ withdrawalScope 1 (848*withdrawalCount input+5*balanceLength input length+11497)
    (by intro observed target evaluated noTimeout
        have release := AllocatorCost.release_call source.code data.context.installed (some none) [localVar "m2"] source rfl
        change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar "m2"])).2.clock≤1 at release
        rw [evaluated] at release
        exact release)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.released "m2" base saved.binding saved.lower saved.upper saved.aligned saved.afterChunks normal
        exact next.withdrawal_cost (saved.after_call _ _ normal) observed evaluated noTimeout) result actual notTimeout
  omega

theorem State.after_transaction_loop_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterTransactionLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤88*VarList.decodedCount input start size+848*withdrawalCount input+5*balanceLength input length+14667 := by
  have bounded := data.transaction_data.2.2
  rw [transaction_shapes.2.2.2.2.2.2.1] at actual
  have paid := ClockCost.sequence_terminating source post _ afterTransactionList (88*VarList.decodedCount input start size+3169)
    (848*withdrawalCount input+5*balanceLength input length+11498)
    (by intro observed target evaluated noTimeout; exact data.list_cost "ntx" 13 _ roots bounded root count observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_list "ntx" 13 _ roots bounded (by decide) root count rootsArena normal
        exact next.after_transaction_list_cost (saved.after_call _ _ normal) observed evaluated noTimeout) result actual notTimeout
  omega

/-- Current transaction loop and its real following list/release/withdrawal
phase. Each actual continuing prefix supplies the next complete payload. -/
theorem State.transaction_loop_suffix_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64) (index : Nat)
    (round : Transactions.RoundState source (VarList.decodedArray array size) roots cursor chunk zeros (Transactions.decodedPointers input blob start)
      (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) index)
    (inside : index≤VarList.decodedCount input start size)
    (geometry : Transactions.Geometry (VarList.decodedArray array size) roots cursor chunk (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
      (VarList.decodedCount input start size) size) (rootsAfter : ch.toNat≤roots.toNat)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source transactionLoopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤Transactions.allowance (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) index+
      (88*VarList.decodedCount input start size+848*withdrawalCount input+5*balanceLength input length+14667) := by
  rw [transaction_shapes.2.2.2.2.2.1] at actual
  exact ClockCost.sequence_terminating source post transactionLoop afterTransactionLoop
    (Transactions.allowance (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) index)
    (88*VarList.decodedCount input start size+848*withdrawalCount input+5*balanceLength input length+14667)
    (by intro observed target evaluated noTimeout; exact Transactions.loop_cost source target _ roots cursor chunk zeros _ _ _ size index inside round geometry observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        obtain ⟨next,position,positionBound,nextRound⟩ := data.after_transaction_loop roots index round inside geometry rootsAfter normal
        have kept := saved.after_program transactionLoop (by rw [loop_shapes.1]; exact .loop _ (transaction_step_local _ (by decide))) normal
        exact next.after_transaction_loop_cost kept roots nextRound.rootsLocal nextRound.count geometry.rootsArena observed evaluated noTimeout)
    result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_transaction_list_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_transaction_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_loop_suffix_cost

import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalSuffixCost
import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalEntry
import InitECandidate.Solver.Input.CurrentHash.AssignedAllocation
import InitECandidate.Solver.Input.ClockCostDeclaredTerminating

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.withdrawal_reset_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p roots : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))) (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n))))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots))) (inputArena : AllocatedBytes.Arena p (44*n))
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAligned : roots.toNat%8=0) (rootsAfter : ch.toNat≤roots.toNat)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterWithdrawalAllocation=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤848*n+5*balanceLength input length+11495 := by
  rw [withdrawal_shapes.2.2.2.1] at actual
  have total : source.clock-post.clock≤0+(848*n+5*balanceLength input length+11495) := by
    apply ClockCost.sequence_terminating source post _ withdrawalLoopAndSuffix 0 (848*n+5*balanceLength input length+11495) _ _ result actual notTimeout
    · intro observed target evaluated noTimeout
      have paid:=ClockCost.assign source.code (ofString "i") (.const 0#64) source rfl
      rw [evaluated] at paid
      exact paid
    · intro middle normal observed target evaluated noTimeout
      have read : eval source (.const 0#64)=some (.val (.word 0#64)) := rfl
      have endpoint := assign_none source middle "i" (.const 0#64) 0#64 read normal
      have next := data.bound "i" 0#64 (by decide)
      have nextSaved : SavedCursor (bind source "i" 0#64) "m2" ch base := saved.of_lookup ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved.binding)
      have round : Withdrawals.RoundState (bind source "i" 0#64) p roots n 0 := ⟨next.context.installed,
        (bind_lookup_other source "i" "wd" 0#64 (by decide)).trans pointer,
        (bind_lookup_other source "i" "roots" 0#64 (by decide)).trans root,
        (bind_lookup_other source "i" "nwd" 0#64 (by decide)).trans count,bind_lookup_same _ _ _⟩
      have clockEq : middle.clock=source.clock := by rw [endpoint]; rfl
      rw [endpoint] at evaluated
      have paid := next.withdrawal_loop_suffix_cost nextSaved p roots n 0 round bounded (by omega) inputArena rootsArena rootsAligned rootsAfter observed evaluated noTimeout
      change source.clock-target.clock≤760*(n-0)+88*n+5*balanceLength input length+11495 at paid
      omega
  simpa only [Nat.zero_add] using total

/-- The real ordinary roots assignment is priced even when allocation fails.
Only its same actual normal return supplies room and the next root arena. -/
theorem State.withdrawal_after_nwd_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))) (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n))))
    (inputArena : AllocatedBytes.Arena p (44*n)) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterNwd=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤848*n+5*balanceLength input length+11497 := by
  rw [withdrawal_shapes.2.2.1] at actual
  have paid : source.clock-post.clock≤2+(848*n+5*balanceLength input length+11495) := ClockCost.sequence_terminating source post _ afterWithdrawalAllocation 2 (848*n+5*balanceLength input length+11495)
    (by intro observed target evaluated noTimeout
        have allocation:=AllocatorCost.alloc_call source.code data.context.installed (some (some (ofString "roots"))) (rootsAllocationArguments "nwd") source rfl
        change source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString "roots"),none)) (ofString "alloc") (rootsAllocationArguments "nwd"))).2.clock≤2 at allocation
        rw [evaluated] at allocation
        exact allocation)
    (by intro middle normal observed target evaluated noTimeout
        let amount := BitVec.ofNat 64 (32*n+32)
        have actualAllocation := AssignedAllocation.normal source middle cursor amount data.context.installed data.context.heap data.context.heapBound "roots" (rootsAllocationArguments "nwd")
          (roots_arguments_read source "nwd" n count) normal
        have kept := actualAllocation.2.2.1
        have ready := data.allocated amount actualAllocation.1 actualAllocation.2.2.2
        have next : State input middle blob record array ch (PersistentAlloc.rounded cursor amount) chunk out zeros length start size := ready.of_frame rfl
          ((kept _ (by decide)).trans data.payload) ((kept _ (by decide)).trans data.raw) ((kept _ (by decide)).trans data.chunks) ((kept _ (by decide)).trans data.output)
        have nextSaved : SavedCursor middle "m2" ch base := saved.of_lookup ((kept _ (by decide)).trans saved.binding)
        have number : amount.toNat=32*n+32 := roots_amount_number n bounded
        have rootsArena : AllocatedBytes.Arena cursor (32*n) := ⟨data.context.heapLower,by have h:=actualAllocation.1; rw [number] at h; omega⟩
        exact next.withdrawal_reset_cost nextSaved p cursor n bounded ((kept _ (by decide)).trans pointer) ((kept _ (by decide)).trans count)
          actualAllocation.2.1 inputArena rootsArena data.context.aligned (by have h:=data.afterChunks; omega) observed evaluated noTimeout)
    result actual notTimeout
  have arithmetic : ∀ a b : Nat,2+(a+b+11495)≤a+b+11497 := by intro a b; omega
  exact Nat.le_trans paid (arithmetic (848*n) (5*balanceLength input length))

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_reset_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_after_nwd_cost

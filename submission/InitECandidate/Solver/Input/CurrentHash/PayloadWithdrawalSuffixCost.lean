import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalState
import InitECandidate.Solver.Input.CurrentHash.PayloadSavedCursor
import InitECandidate.Solver.Input.CurrentHash.PayloadFinalCost

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.after_withdrawal_list_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterWithdrawalList=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤5*balanceLength input length+8326 := by
  rw [withdrawal_shapes.2.2.2.2.2.2] at actual
  have paid := ClockCost.sequence_terminating source post _ finalFields 1 (5*balanceLength input length+8325)
    (by intro observed target evaluated noTimeout
        have release := AllocatorCost.release_call source.code data.context.installed (some none) [localVar "m2"] source rfl
        change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar "m2"])).2.clock≤1 at release
        rw [evaluated] at release
        exact release)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.released "m2" base saved.binding saved.lower saved.upper saved.aligned saved.afterChunks normal
        exact next.final_cost observed evaluated noTimeout) result actual notTimeout
  omega

theorem State.after_withdrawal_loop_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n)))) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterWithdrawalLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤88*n+5*balanceLength input length+11495 := by
  rw [withdrawal_shapes.2.2.2.2.2.1] at actual
  have paid := ClockCost.sequence_terminating source post _ afterWithdrawalList (88*n+3169) (5*balanceLength input length+8326)
    (by intro observed target evaluated noTimeout; exact data.list_cost "nwd" 14 n roots bounded root count observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have next := data.after_list "nwd" 14 n roots bounded (by decide) root count rootsArena normal
        have kept := saved.after_call _ _ normal
        exact next.after_withdrawal_list_cost kept observed evaluated noTimeout) result actual notTimeout
  omega

/-- Current withdrawal loop and its actual following list/release/final hash
phase, carrying the same decoded payload and saved cursor between calls. -/
theorem State.withdrawal_loop_suffix_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p roots : BitVec 64) (n index : Nat)
    (round : Withdrawals.RoundState source p roots n index) (bounded : n≤134217728) (inside : index≤n)
    (inputArena : AllocatedBytes.Arena p (44*n)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAligned : roots.toNat%8=0) (rootsAfter : ch.toNat≤roots.toNat)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source withdrawalLoopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤760*(n-index)+88*n+5*balanceLength input length+11495 := by
  rw [withdrawal_shapes.2.2.2.2.1] at actual
  have paid := ClockCost.sequence_terminating source post withdrawalLoop afterWithdrawalLoop (760*(n-index)) (88*n+5*balanceLength input length+11495)
    (by intro observed target evaluated noTimeout; exact Withdrawals.loop_cost source target p roots n index bounded inside round observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        obtain ⟨next,position,positionBound,nextRound⟩ := data.after_withdrawal_loop p roots n index round bounded inside inputArena rootsArena rootsAligned rootsAfter normal
        have kept := saved.after_program withdrawalLoop (by rw [loop_shapes.2.2.1]; exact .loop _ (withdrawal_step_local _ (by decide))) normal
        exact next.after_withdrawal_loop_cost kept roots n bounded nextRound.root nextRound.count rootsArena observed evaluated noTimeout)
    result actual notTimeout
  omega

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_withdrawal_list_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_withdrawal_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_loop_suffix_cost

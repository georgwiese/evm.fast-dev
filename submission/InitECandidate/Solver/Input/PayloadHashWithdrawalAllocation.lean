import InitECandidate.Solver.Input.PayloadHashWithdrawalCounter
import InitECandidate.Solver.Input.PayloadHashRootsState

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.WithdrawalAllocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem retained (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64)
    (name : String) (different : ofString "roots"≠ofString name) :
    (RootsPhase.next .withdrawals data source ch).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other _ "roots" name _ different

/-- Actual original assigned roots allocation, counter reset, withdrawal
loop and complete payload tail. Failure costs include the allocator trap. -/
theorem cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterNwd=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+732*data.withdrawalCount+50636 := by
  rw [withdrawal_shapes.2.2.1] at run
  have price := ClockCost.sequence_terminating source post (RootsPhase.localCall .withdrawals) afterWithdrawalAllocation 2 (BalancePhase.price data+732*data.withdrawalCount+50634)
    (fun observed target evaluated notTimeout=>RootsPhase.local_cost .withdrawals source target actual.ready.workspace.sha.installed observed evaluated)
    (by intro middle normal observed target evaluated notTimeout
        have same := RootsPhase.local_normal .withdrawals data origin source middle lower upper budget ch out mark stp accel chunk zeros oldRoots layout actual geometry roots count normal
        subst middle
        have ready := RootsPhase.next_state .withdrawals data origin source lower upper budget ch out mark stp accel chunk zeros layout actual geometry
        exact WithdrawalCounter.cost data origin _ target lower upper budget ch out mark stp accel chunk zeros oldIndex image layout ready geometry separation small before
          ((retained data source ch "wd" (by decide)).trans pointer)
          (bind_lookup_same _ "roots" (chunksCursor ch))
          ((retained data source ch "nwd" (by decide)).trans count)
          ((retained data source ch "i" (by decide)).trans position)
          ((retained data source ch "m2" (by decide)).trans saved) observed evaluated notTimeout)
    result run notTimeout
  rw [Nat.add_left_comm 2 (BalancePhase.price data+732*data.withdrawalCount)] at price
  exact price

theorem normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterNwd=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.2.2.1] at run
  have safe : LocalPrefix (ofString "raw") (RootsPhase.localCall .withdrawals) := .call (some (ofString "roots")) _ _ (by intro name same; cases same; decide)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post (RootsPhase.localCall .withdrawals) afterWithdrawalAllocation value (safe.summary_full source).2.1 run
  have same := RootsPhase.local_normal .withdrawals data origin source middle lower upper budget ch out mark stp accel chunk zeros oldRoots layout actual geometry roots count normal
  subst middle
  have ready := RootsPhase.next_state .withdrawals data origin source lower upper budget ch out mark stp accel chunk zeros layout actual geometry
  exact WithdrawalCounter.normal data origin _ post lower upper budget ch out mark stp accel chunk zeros oldIndex image layout ready geometry outputGeometry separation small before
    ((retained data source ch "wd" (by decide)).trans pointer)
    (bind_lookup_same _ "roots" (chunksCursor ch))
    ((retained data source ch "nwd" (by decide)).trans count)
    ((retained data source ch "i" (by decide)).trans position)
    ((retained data source ch "m2" (by decide)).trans saved) value remaining

end InitECandidate.Solver.Input.PayloadHash.WithdrawalAllocation
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalAllocation.retained
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalAllocation.cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalAllocation.normal

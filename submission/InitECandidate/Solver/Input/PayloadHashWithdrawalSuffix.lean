import InitECandidate.Solver.Input.PayloadHashWithdrawalState
import InitECandidate.Solver.Input.PayloadHashListState
import InitECandidate.Solver.Input.PayloadHashReleaseState
import InitECandidate.Solver.Input.PayloadHashFinalFields

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem loop_arithmetic (spent count balance : Nat)
    (price : spent≤617*count+(balance+115*count+50634)) : spent≤balance+732*count+50634 := by
  rw [←Nat.add_assoc (617*count) (balance+115*count) 50634,
    Nat.add_left_comm (617*count) balance (115*count),←Nat.add_mul 617 115 count] at price
  exact price

theorem after_list_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterWithdrawalList=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+26427 := by
  rw [withdrawal_shapes.2.2.2.2.2.2] at run
  have price := ClockCost.sequence_terminating source post ReleasePhase.call finalFields 1 (BalancePhase.price data+26426)
    (fun observed target evaluated notTimeout=>ReleasePhase.call_cost source target actual.ready.workspace.sha.installed observed evaluated)
    (by intro middle normal observed target evaluated notTimeout
        have next := ReleasePhase.call_normal origin source middle lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) (chunksCursor ch) mark stp accel chunk zeros actual saved normal
        exact FinalFields.final_fields_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros image layout next geometry separation small before observed evaluated notTimeout)
    result run notTimeout
  clear run actual image geometry layout separation
  omega

theorem after_list_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterWithdrawalList=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.2.2.2.2.2.2] at run
  have safe : LocalPrefix (ofString "raw") ReleasePhase.call := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post ReleasePhase.call finalFields value (safe.summary_full source).2.1 run
  have next := ReleasePhase.call_normal origin source middle lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) (chunksCursor ch) mark stp accel chunk zeros actual saved normal
  exact FinalFields.final_fields_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros image layout next geometry outputGeometry separation small before value remaining

theorem after_loop_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterWithdrawalLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+115*data.withdrawalCount+50634 := by
  rw [withdrawal_shapes.2.2.2.2.2.1] at run
  have price := ClockCost.sequence_terminating source post (ListPhase.Kind.call .withdrawals) afterWithdrawalList (115*data.withdrawalCount+24207) (BalancePhase.price data+26427)
    (fun observed target evaluated notTimeout=>ListPhase.call_cost .withdrawals data origin source target lower upper budget ch out mark stp accel chunk zeros layout actual geometry roots count observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have next := ListPhase.call_normal .withdrawals data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before roots count normal
        have nextSaved := (CallNormal.ignored_lookup source middle (ofString "m2") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .withdrawals) normal).trans saved
        exact after_list_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros image layout next geometry separation small before nextSaved observed evaluated notTimeout)
    result run notTimeout
  clear run actual image geometry layout separation
  omega

theorem after_loop_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterWithdrawalLoop=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.2.2.2.2.2.1] at run
  have safe : LocalPrefix (ofString "raw") (ListPhase.Kind.call .withdrawals) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post (ListPhase.Kind.call .withdrawals) afterWithdrawalList value (safe.summary_full source).2.1 run
  have next := ListPhase.call_normal .withdrawals data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before roots count normal
  have nextSaved := (CallNormal.ignored_lookup source middle (ofString "m2") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .withdrawals) normal).trans saved
  exact after_list_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros image layout next geometry outputGeometry separation small before nextSaved value remaining

/-- Original withdrawal loop plus its actual list hash, m2 release and final
payload tail. Cost uses the real record count and actual balance length. -/
theorem loop_suffix_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalLoopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+732*data.withdrawalCount+50634 := by
  rw [withdrawal_shapes.2.2.2.2.1] at run
  have price := ClockCost.sequence_terminating source post withdrawalLoop afterWithdrawalLoop (617*data.withdrawalCount) (BalancePhase.price data+115*data.withdrawalCount+50634)
    (fun observed target evaluated notTimeout=>WithdrawalPhase.loop_cost data origin source target lower upper budget ch out mark stp accel chunk zeros layout actual geometry pointer count roots position observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have next := WithdrawalPhase.loop_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before pointer count roots position normal
        have other (name : String) (different : ofString name≠ofString "i") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
          have summary := (Withdrawals.loop_local (ofString name) different).summary_full source
          unfold LocalSummary at summary
          rw [normal] at summary
          exact summary.1 rfl
        exact after_loop_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros image layout next geometry separation small before
          ((other "roots" (by decide)).trans roots) ((other "nwd" (by decide)).trans count) ((other "m2" (by decide)).trans saved) observed evaluated notTimeout)
    result run notTimeout
  exact loop_arithmetic _ _ _ price

theorem loop_suffix_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source withdrawalLoopAndSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.2.2.2.2.1] at run
  have safe := Withdrawals.loop_local (ofString "raw") (by decide)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post withdrawalLoop afterWithdrawalLoop value (safe.summary_full source).2.1 run
  have next := WithdrawalPhase.loop_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before pointer count roots position normal
  have other (name : String) (different : ofString name≠ofString "i") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (Withdrawals.loop_local (ofString name) different).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact after_loop_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros image layout next geometry outputGeometry separation small before
    ((other "roots" (by decide)).trans roots) ((other "nwd" (by decide)).trans count) ((other "m2" (by decide)).trans saved) value remaining

end InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix

#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.after_list_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.after_list_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.after_loop_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.after_loop_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.loop_suffix_cost

#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalSuffix.loop_suffix_normal

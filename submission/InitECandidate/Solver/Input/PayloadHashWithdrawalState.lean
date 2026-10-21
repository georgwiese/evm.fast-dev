import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall

namespace InitECandidate.Solver.Input.PayloadHash.WithdrawalPhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def cursor (data : Description) (ch : BitVec 64) := afterRoots (chunksCursor ch) data.withdrawalCount

theorem current_round (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (countCell : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) :
    Withdrawals.RoundState source data.withdrawals (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.withdrawalCount 0 :=
  ⟨actual.ready.workspace,pointer,countCell,rootsCell,position,actual.ready.heap⟩

/-- Actual initialized original withdrawal loop in the enclosing payload
scope, including all non-timeout failure prefixes. -/
theorem loop_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (countCell : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤617*data.withdrawalCount := by
  have ready := current_round data origin source lower upper ch out mark stp accel chunk zeros actual pointer countCell rootsCell position
  have mapped := (data.withdrawal_geometry lower upper budget ch layout geometry).1
  have price := Withdrawals.loop_cost source post data.withdrawals (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.withdrawalCount 0 (Nat.zero_le _) ready mapped result run notTimeout
  simpa only [Nat.sub_zero] using price

/-- Actual normal exit retains the full payload caller/input relation at
its original withdrawal temporary cursor. -/
theorem loop_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (countCell : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (run : evaluateHOLFiniteState source withdrawalLoop=(none,post)) :
    StaticFields.State origin post lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros := by
  have ready := current_round data origin source lower upper ch out mark stp accel chunk zeros actual pointer countCell rootsCell position
  have mapped := (data.withdrawal_geometry lower upper budget ch layout geometry).1
  obtain ⟨index,inside,next⟩ := Withdrawals.loop_normal source post data.withdrawals (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.withdrawalCount 0 (Nat.zero_le _) ready mapped run
  apply actual.after_program origin source post lower upper data.payload data.raw ch out (cursor data ch) (cursor data ch) mark stp accel chunk zeros withdrawalLoop run next.heap
  · intro key different; exact Withdrawals.loop_globals key source.code actual.ready.workspace.sha.installed different
  · intro name different
    have summary := (Withdrawals.loop_local (ofString name) different).summary_full source
    unfold LocalSummary at summary
    rw [run] at summary
    exact summary.1 rfl
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have static := (data.static_geometry lower upper budget ch layout geometry).1
    exact Withdrawals.loop_memory source post data.withdrawals (chunksCursor ch) (cursor data ch) stp accel chunk zeros query data.withdrawalCount 0
      (Nat.zero_le _) ready mapped protection (by have h:=static.chunksBefore; omega) run

end InitECandidate.Solver.Input.PayloadHash.WithdrawalPhase

#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalPhase.current_round
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalPhase.loop_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalPhase.loop_normal

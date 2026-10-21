import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall

namespace InitECandidate.Solver.Input.PayloadHash.TransactionPhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def cursor (data : Description) (ch : BitVec 64) := afterRoots (chunksCursor ch) data.transactionCount

theorem current_round (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) :
    Transactions.RoundState source data.transactions (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.transactionPointer data.transactionLength data.transactionCount 0 :=
  ⟨actual.ready.workspace,arrayCell,countCell,rootsCell,position,data.current_rows origin source lower upper budget image layout actual.input,actual.ready.heap⟩

/-- Original transaction-loop bound at its actual initialized payload scope.
Only actual decoded row lengths/count are charged, with failures retained. -/
theorem loop_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (before : upper≤ch.toNat)
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤4*VarList.sumPrefix data.transactionLength data.transactionCount+24399*data.transactionCount := by
  have ready := current_round data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual arrayCell countCell rootsCell position
  have mapped := (data.transaction_geometry lower upper budget ch stp accel chunk layout geometry separation before).1
  have price := Transactions.loop_cost source post data.transactions (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.transactionPointer data.transactionLength data.transactionCount budget 0
    (Nat.zero_le _) ready mapped result run notTimeout
  simpa only [Transactions.allowance,VarList.sumPrefix,Nat.sub_zero] using price

/-- Actual normal loop exit reestablishes the whole payload input/caller
relation at the same temporary cursor; no later list hash is assumed. -/
theorem loop_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (rootsCell : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (run : evaluateHOLFiniteState source transactionLoop=(none,post)) :
    StaticFields.State origin post lower upper data.payload data.raw ch out (cursor data ch) mark stp accel chunk zeros := by
  have ready := current_round data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual arrayCell countCell rootsCell position
  have mapped := (data.transaction_geometry lower upper budget ch stp accel chunk layout geometry separation before).1
  obtain ⟨index,inside,next⟩ := Transactions.loop_normal source post data.transactions (chunksCursor ch) (cursor data ch) stp accel chunk zeros data.transactionPointer data.transactionLength data.transactionCount budget 0 (Nat.zero_le _) ready mapped run
  apply actual.after_program origin source post lower upper data.payload data.raw ch out (cursor data ch) (cursor data ch) mark stp accel chunk zeros transactionLoop run next.heap
  · intro key different; exact Transactions.loop_globals key source.code actual.ready.workspace.sha.installed different
  · intro name different
    have summary := (Transactions.loop_local (ofString name) different).summary_full source
    unfold LocalSummary at summary
    rw [run] at summary
    exact summary.1 rfl
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have static := (data.static_geometry lower upper budget ch layout geometry).1
    exact Transactions.loop_memory source post data.transactions (chunksCursor ch) (cursor data ch) stp accel chunk zeros query data.transactionPointer data.transactionLength data.transactionCount budget 0
      (Nat.zero_le _) ready mapped protection (by have h:=static.chunksBefore; omega) run

end InitECandidate.Solver.Input.PayloadHash.TransactionPhase

#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPhase.current_round
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPhase.loop_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPhase.loop_normal

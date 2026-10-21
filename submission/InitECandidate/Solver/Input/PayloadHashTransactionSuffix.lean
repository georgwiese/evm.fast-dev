import InitECandidate.Solver.Input.PayloadHashTransactionState
import InitECandidate.Solver.Input.PayloadHashWithdrawalScope

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.TransactionSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def withdrawalPrice (data : Description) := BalancePhase.price data+732*data.withdrawalCount+50636
def afterListPrice (data : Description) := 1+withdrawalPrice data
def afterLoopPrice (data : Description) := (115*data.transactionCount+24207)+afterListPrice data
def loopSuffixPrice (data : Description) := (4*VarList.sumPrefix data.transactionLength data.transactionCount+24399*data.transactionCount)+afterLoopPrice data

/-- The actual transaction loop produces a word-valued exit counter for
its original following withdrawal reset, without assuming later success. -/
theorem exit_counter (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (run : evaluateHOLFiniteState source transactionLoop=(none,post)) :
    ∃ index : BitVec 64,post.locals.lookup (ofString "i")=some (.val (.word index)) := by
  have ready := TransactionPhase.current_round data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual array count roots position
  have mapped := (data.transaction_geometry lower upper budget ch stp accel chunk layout geometry separation before).1
  obtain ⟨index,inside,next⟩ := Transactions.loop_normal source post data.transactions (chunksCursor ch) (TransactionPhase.cursor data ch) stp accel chunk zeros data.transactionPointer data.transactionLength data.transactionCount budget 0 (Nat.zero_le _) ready mapped run
  exact ⟨BitVec.ofNat 64 index,next.position⟩

theorem after_list_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionList=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤afterListPrice data := by
  rw [transaction_shapes.2.2.2.2.2.2.2] at run
  exact ClockCost.sequence_terminating source post ReleasePhase.call withdrawalScope 1 (withdrawalPrice data)
    (fun observed target evaluated notTimeout=>ReleasePhase.call_cost source target actual.ready.workspace.sha.installed observed evaluated)
    (by intro middle normal observed target evaluated notTimeout
        have next := ReleasePhase.call_normal origin source middle lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) (chunksCursor ch) mark stp accel chunk zeros actual saved normal
        exact WithdrawalScope.scope_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros (chunksCursor ch) oldIndex image layout next geometry separation small before
          ((CallNormal.ignored_lookup source middle (ofString "roots") (ofString "heap_release") [localVar "m2"] normal).trans roots) ((CallNormal.ignored_lookup source middle (ofString "i") (ofString "heap_release") [localVar "m2"] normal).trans position) ((CallNormal.ignored_lookup source middle (ofString "m2") (ofString "heap_release") [localVar "m2"] normal).trans saved) observed evaluated notTimeout)
    result run notTimeout

theorem after_list_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTransactionList=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.2.2.2.2.2] at run
  have safe : LocalPrefix (ofString "raw") ReleasePhase.call := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post ReleasePhase.call withdrawalScope value (safe.summary_full source).2.1 run
  have next := ReleasePhase.call_normal origin source middle lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) (chunksCursor ch) mark stp accel chunk zeros actual saved normal
  exact WithdrawalScope.scope_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros (chunksCursor ch) oldIndex image layout next geometry outputGeometry separation small before
    ((CallNormal.ignored_lookup source middle (ofString "roots") (ofString "heap_release") [localVar "m2"] normal).trans roots) ((CallNormal.ignored_lookup source middle (ofString "i") (ofString "heap_release") [localVar "m2"] normal).trans position) ((CallNormal.ignored_lookup source middle (ofString "m2") (ofString "heap_release") [localVar "m2"] normal).trans saved) value remaining

theorem after_loop_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤afterLoopPrice data := by
  rw [transaction_shapes.2.2.2.2.2.2.1] at run
  exact ClockCost.sequence_terminating source post (ListPhase.Kind.call .transactions) afterTransactionList (115*data.transactionCount+24207) (afterListPrice data)
    (fun observed target evaluated notTimeout=>ListPhase.call_cost .transactions data origin source target lower upper budget ch out mark stp accel chunk zeros layout actual geometry roots count observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have next := ListPhase.call_normal .transactions data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before roots count normal
        exact after_list_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros oldIndex image layout next geometry separation small before
          ((CallNormal.ignored_lookup source middle (ofString "roots") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans roots) ((CallNormal.ignored_lookup source middle (ofString "i") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans position) ((CallNormal.ignored_lookup source middle (ofString "m2") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans saved) observed evaluated notTimeout)
    result run notTimeout

theorem after_loop_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTransactionLoop=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.2.2.2.2.1] at run
  have safe : LocalPrefix (ofString "raw") (ListPhase.Kind.call .transactions) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post (ListPhase.Kind.call .transactions) afterTransactionList value (safe.summary_full source).2.1 run
  have next := ListPhase.call_normal .transactions data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry separation small before roots count normal
  exact after_list_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros oldIndex image layout next geometry outputGeometry separation small before
    ((CallNormal.ignored_lookup source middle (ofString "roots") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans roots) ((CallNormal.ignored_lookup source middle (ofString "i") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans position) ((CallNormal.ignored_lookup source middle (ofString "m2") (ofString "htr_plist_chunks") (ListPhase.Kind.arguments .transactions) normal).trans saved) value remaining

theorem loop_suffix_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionLoopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤loopSuffixPrice data := by
  rw [transaction_shapes.2.2.2.2.2.1] at run
  exact ClockCost.sequence_terminating source post transactionLoop afterTransactionLoop (4*VarList.sumPrefix data.transactionLength data.transactionCount+24399*data.transactionCount) (afterLoopPrice data)
    (fun observed target evaluated notTimeout=>TransactionPhase.loop_cost data origin source target lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation before array count roots position observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have next := TransactionPhase.loop_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation small before array count roots position normal
        obtain ⟨exitIndex,indexCell⟩ := exit_counter data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation before array count roots position normal
        have other (name : String) (different : ofString name≠ofString "i") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
          have summary := (Transactions.loop_local (ofString name) different).summary_full source
          unfold LocalSummary at summary
          rw [normal] at summary
          exact summary.1 rfl
        exact after_loop_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros exitIndex image layout next geometry separation small before
          ((other "roots" (by decide)).trans roots) ((other "ntx" (by decide)).trans count) indexCell ((other "m2" (by decide)).trans saved) observed evaluated notTimeout)
    result run notTimeout

theorem loop_suffix_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source transactionLoopAndSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.2.2.2.1] at run
  have safe : LocalPrefix (ofString "raw") transactionLoop := Transactions.loop_local (ofString "raw") (by decide)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post transactionLoop afterTransactionLoop value (safe.summary_full source).2.1 run
  have next := TransactionPhase.loop_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation small before array count roots position normal
  obtain ⟨exitIndex,indexCell⟩ := exit_counter data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation before array count roots position normal
  have other (name : String) (different : ofString name≠ofString "i") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (Transactions.loop_local (ofString name) different).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact after_loop_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros exitIndex image layout next geometry outputGeometry separation small before
    ((other "roots" (by decide)).trans roots) ((other "ntx" (by decide)).trans count) indexCell ((other "m2" (by decide)).trans saved) value remaining

end InitECandidate.Solver.Input.PayloadHash.TransactionSuffix
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.exit_counter
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.after_list_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.after_list_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.after_loop_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.after_loop_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.loop_suffix_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionSuffix.loop_suffix_normal

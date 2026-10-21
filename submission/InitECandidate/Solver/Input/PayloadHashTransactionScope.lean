import InitECandidate.Solver.Input.PayloadHashTransactionPrefix
import InitECandidate.Solver.Input.HeapMarkTrace

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.TransactionScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def price (data : Description) := 1+(1+TransactionSuffix.loopSuffixPrice data)

theorem after_count_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterNtx=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price data := by
  rw [transaction_shapes.2.2.1] at run
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post (chunksCursor ch) "m2" afterSecondMark actual.ready.heap
    (HeapScope.mark_original_code source.code actual.ready.workspace.sha.installed) result run notTimeout
  have clocked := actual.with_clock origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros (source.clock-1)
  have ready := clocked.bind_current origin _ lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "m2" (chunksCursor ch) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := TransactionPrefix.allocation_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before
    ((bind_lookup_other {source with clock:=source.clock-1} "m2" "txs" (chunksCursor ch) (by decide)).trans array)
    ((bind_lookup_other {source with clock:=source.clock-1} "m2" "ntx" (chunksCursor ch) (by decide)).trans count)
    (bind_lookup_same _ "m2" (chunksCursor ch)) result remaining notTimeout
  rw [endpoint]
  have monotone := evaluateHOLFiniteState_clock_le (bind {source with clock:=source.clock-1} "m2" (chunksCursor ch)) afterSecondMark
  rw [remaining] at monotone
  exact ClockCost.funded_tick source.clock inner.clock (1+TransactionSuffix.loopSuffixPrice data) funded monotone checked

theorem after_count_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterNtx=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.1] at run
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post (chunksCursor ch) "m2" afterSecondMark actual.ready.heap
    (HeapScope.mark_original_code source.code actual.ready.workspace.sha.installed) (some (.returned value)) run (by simp)
  have clocked := actual.with_clock origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros (source.clock-1)
  have ready := clocked.bind_current origin _ lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "m2" (chunksCursor ch) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := TransactionPrefix.allocation_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before
    ((bind_lookup_other {source with clock:=source.clock-1} "m2" "txs" (chunksCursor ch) (by decide)).trans array)
    ((bind_lookup_other {source with clock:=source.clock-1} "m2" "ntx" (chunksCursor ch) (by decide)).trans count)
    (bind_lookup_same _ "m2" (chunksCursor ch)) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

theorem after_array_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTxs=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price data := by
  rw [transaction_shapes.2.1] at run
  have read : eval source (fieldExpression 40)=some (.val (.word (BitVec.ofNat 64 data.transactionCount))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (40,BitVec.ofNat 64 data.transactionCount) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "ntx" (fieldExpression 40) (BitVec.ofNat 64 data.transactionCount) afterNtx result read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "ntx" (BitVec.ofNat 64 data.transactionCount) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_count_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before
    ((bind_lookup_other source "ntx" "txs" (BitVec.ofNat 64 data.transactionCount) (by decide)).trans array)
    (bind_lookup_same source "ntx" (BitVec.ofNat 64 data.transactionCount)) result remaining notTimeout
  rw [endpoint]
  exact checked

theorem after_array_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTxs=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.1] at run
  have read : eval source (fieldExpression 40)=some (.val (.word (BitVec.ofNat 64 data.transactionCount))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (40,BitVec.ofNat 64 data.transactionCount) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "ntx" (fieldExpression 40) (BitVec.ofNat 64 data.transactionCount) afterNtx (some (.returned value)) read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "ntx" (BitVec.ofNat 64 data.transactionCount) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_count_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before
    ((bind_lookup_other source "ntx" "txs" (BitVec.ofNat 64 data.transactionCount) (by decide)).trans array)
    (bind_lookup_same source "ntx" (BitVec.ofNat 64 data.transactionCount)) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

theorem scope_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionScope=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price data := by
  rw [transaction_shapes.1] at run
  have read : eval source (fieldExpression 32)=some (.val (.word (data.transactions))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (32,data.transactions) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "txs" (fieldExpression 32) (data.transactions) afterTxs result read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "txs" (data.transactions) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_array_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before
    (bind_lookup_same source "txs" (data.transactions)) result remaining notTimeout
  rw [endpoint]
  exact checked

theorem scope_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source transactionScope=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.1] at run
  have read : eval source (fieldExpression 32)=some (.val (.word (data.transactions))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (32,data.transactions) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "txs" (fieldExpression 32) (data.transactions) afterTxs (some (.returned value)) read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "txs" (data.transactions) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_array_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before
    (bind_lookup_same source "txs" (data.transactions)) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash.TransactionScope
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.after_count_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.after_count_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.after_array_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.after_array_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.scope_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionScope.scope_normal

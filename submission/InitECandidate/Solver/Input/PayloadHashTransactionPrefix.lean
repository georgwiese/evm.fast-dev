import InitECandidate.Solver.Input.PayloadHashTransactionSuffix
import InitECandidate.Solver.Input.ClockCostFundedTick

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.TransactionPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem retained (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64)
    (name : String) (different : ofString "roots"≠ofString name) :
    (RootsPhase.next .transactions data source ch).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  bind_lookup_other _ "roots" name _ different

theorem after_roots_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTxRoots=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤TransactionSuffix.loopSuffixPrice data := by
  rw [transaction_shapes.2.2.2.2.1] at run
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "i" (.const 0#64) 0#64 transactionLoopAndSuffix result rfl run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros "i" 0#64 ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := TransactionSuffix.loop_suffix_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before
    ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans roots)
    ((bind_lookup_other source "i" "ntx" 0#64 (by decide)).trans count)
    ((bind_lookup_other source "i" "txs" 0#64 (by decide)).trans array)
    (bind_lookup_same source "i" 0#64)
    ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved) result remaining notTimeout
  rw [endpoint]
  exact checked

theorem after_roots_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTxRoots=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.2.2.1] at run
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "i" (.const 0#64) 0#64 transactionLoopAndSuffix (some (.returned value)) rfl run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (TransactionPhase.cursor data ch) mark stp accel chunk zeros "i" 0#64 ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := TransactionSuffix.loop_suffix_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before
    ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans roots)
    ((bind_lookup_other source "i" "ntx" 0#64 (by decide)).trans count)
    ((bind_lookup_other source "i" "txs" 0#64 (by decide)).trans array)
    (bind_lookup_same source "i" 0#64)
    ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

theorem allocation_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterSecondMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤1+TransactionSuffix.loopSuffixPrice data := by
  rw [transaction_shapes.2.2.2.1] at run
  have room := (RootsPhase.geometry .transactions data lower upper budget ch layout geometry).1
  have args := RootsPhase.arguments_read .transactions data source count
  obtain ⟨funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "roots" (rootsAllocationArguments "ntx") afterTxRoots (chunksCursor ch) (RootsPhase.amount .transactions data)
    args (PersistentAlloc.original_code source.code actual.ready.workspace.sha.installed) actual.ready.heap room result run notTimeout
  have ready := RootsPhase.next_state .transactions data origin source lower upper budget ch out mark stp accel chunk zeros layout actual geometry
  have checked := after_roots_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before
    ((retained data source ch "txs" (by decide)).trans array)
    ((retained data source ch "ntx" (by decide)).trans count)
    (bind_lookup_same _ "roots" (chunksCursor ch))
    ((retained data source ch "m2" (by decide)).trans saved) result remaining notTimeout
  rw [endpoint]
  change evaluateHOLFiniteState (RootsPhase.next .transactions data source ch) afterTxRoots=(result,inner) at remaining
  have monotone := evaluateHOLFiniteState_clock_le (RootsPhase.next .transactions data source ch) afterTxRoots
  rw [remaining] at monotone
  exact ClockCost.funded_tick source.clock inner.clock (TransactionSuffix.loopSuffixPrice data) funded monotone checked

theorem allocation_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (array : source.locals.lookup (ofString "txs")=some (.val (.word data.transactions)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 data.transactionCount))))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterSecondMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [transaction_shapes.2.2.2.1] at run
  have room := (RootsPhase.geometry .transactions data lower upper budget ch layout geometry).1
  have args := RootsPhase.arguments_read .transactions data source count
  obtain ⟨funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "roots" (rootsAllocationArguments "ntx") afterTxRoots (chunksCursor ch) (RootsPhase.amount .transactions data)
    args (PersistentAlloc.original_code source.code actual.ready.workspace.sha.installed) actual.ready.heap room (some (.returned value)) run (by simp)
  have ready := RootsPhase.next_state .transactions data origin source lower upper budget ch out mark stp accel chunk zeros layout actual geometry
  have checked := after_roots_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before
    ((retained data source ch "txs" (by decide)).trans array)
    ((retained data source ch "ntx" (by decide)).trans count)
    (bind_lookup_same _ "roots" (chunksCursor ch))
    ((retained data source ch "m2" (by decide)).trans saved) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash.TransactionPrefix
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPrefix.retained
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPrefix.after_roots_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPrefix.after_roots_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPrefix.allocation_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.TransactionPrefix.allocation_normal

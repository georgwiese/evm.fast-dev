import InitECandidate.Solver.Input.PayloadHashWithdrawalSuffix
import InitECandidate.Solver.Input.PayloadHashStatePrefix

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.WithdrawalCounter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original assignment resets the existing transaction counter before
entering the withdrawal loop; it retains the real input and caller state. -/
theorem initialized (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros) :
    StaticFields.State origin (bind source "i" 0#64) lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros :=
  actual.bind_current origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros "i" 0#64
    ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros old : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterWithdrawalAllocation=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+732*data.withdrawalCount+50634 := by
  have assigned := StateSteps.assign_execute source "i" (.const 0#64) old 0#64 position rfl
  rw [withdrawal_shapes.2.2.2.1,StateSteps.next_sequence source (bind source "i" 0#64) _ _ assigned (Nat.le_refl _)] at run
  exact WithdrawalSuffix.loop_suffix_cost data origin (bind source "i" 0#64) post lower upper budget ch out mark stp accel chunk zeros image layout
    (initialized data origin source lower upper ch out mark stp accel chunk zeros actual) geometry separation small before
    ((bind_lookup_other source "i" "wd" 0#64 (by decide)).trans pointer)
    ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans roots)
    ((bind_lookup_other source "i" "nwd" 0#64 (by decide)).trans count)
    (bind_lookup_same source "i" 0#64)
    ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved) result run notTimeout

theorem normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros old : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (WithdrawalPhase.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word old)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterWithdrawalAllocation=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have assigned := StateSteps.assign_execute source "i" (.const 0#64) old 0#64 position rfl
  rw [withdrawal_shapes.2.2.2.1,StateSteps.next_sequence source (bind source "i" 0#64) _ _ assigned (Nat.le_refl _)] at run
  exact WithdrawalSuffix.loop_suffix_normal data origin (bind source "i" 0#64) post lower upper budget ch out mark stp accel chunk zeros image layout
    (initialized data origin source lower upper ch out mark stp accel chunk zeros actual) geometry outputGeometry separation small before
    ((bind_lookup_other source "i" "wd" 0#64 (by decide)).trans pointer)
    ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans roots)
    ((bind_lookup_other source "i" "nwd" 0#64 (by decide)).trans count)
    (bind_lookup_same source "i" 0#64)
    ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved) value run

end InitECandidate.Solver.Input.PayloadHash.WithdrawalCounter

#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalCounter.initialized
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalCounter.cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalCounter.normal

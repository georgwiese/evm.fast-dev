import InitECandidate.Solver.Input.PayloadHashWithdrawalAllocation
import InitECandidate.Solver.Input.ScalarScopeTrace

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.WithdrawalScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_wd_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterWd=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+732*data.withdrawalCount+50636 := by
  rw [withdrawal_shapes.2.1] at run
  have read : eval source (fieldExpression 56)=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (56,BitVec.ofNat 64 data.withdrawalCount) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "nwd" (fieldExpression 56) (BitVec.ofNat 64 data.withdrawalCount) afterNwd result read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "nwd" (BitVec.ofNat 64 data.withdrawalCount) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := WithdrawalAllocation.cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros oldRoots oldIndex image layout ready geometry separation small before
    ((bind_lookup_other source "nwd" "wd" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans pointer)
    ((bind_lookup_other source "nwd" "roots" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans roots)
    (bind_lookup_same source "nwd" (BitVec.ofNat 64 data.withdrawalCount))
    ((bind_lookup_other source "nwd" "i" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans position)
    ((bind_lookup_other source "nwd" "m2" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans saved) result remaining notTimeout
  rw [endpoint]
  exact checked

theorem scope_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalScope=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤BalancePhase.price data+732*data.withdrawalCount+50636 := by
  rw [withdrawal_shapes.1] at run
  have read : eval source (fieldExpression 48)=some (.val (.word (data.withdrawals))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (48,data.withdrawals) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "wd" (fieldExpression 48) (data.withdrawals) afterWd result read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "wd" (data.withdrawals) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_wd_cost data origin _ inner lower upper budget ch out mark stp accel chunk zeros oldRoots oldIndex image layout ready geometry separation small before
    ((bind_lookup_other source "wd" "roots" (data.withdrawals) (by decide)).trans roots)
    ((bind_lookup_other source "wd" "i" (data.withdrawals) (by decide)).trans position)
    ((bind_lookup_other source "wd" "m2" (data.withdrawals) (by decide)).trans saved)
    (bind_lookup_same source "wd" (data.withdrawals)) result remaining notTimeout
  rw [endpoint]
  exact checked

theorem after_wd_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word data.withdrawals)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterWd=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.2.1] at run
  have read : eval source (fieldExpression 56)=some (.val (.word (BitVec.ofNat 64 data.withdrawalCount))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (56,BitVec.ofNat 64 data.withdrawalCount) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "nwd" (fieldExpression 56) (BitVec.ofNat 64 data.withdrawalCount) afterNwd (some (.returned value)) read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "nwd" (BitVec.ofNat 64 data.withdrawalCount) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := WithdrawalAllocation.normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros oldRoots oldIndex image layout ready geometry outputGeometry separation small before
    ((bind_lookup_other source "nwd" "wd" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans pointer)
    ((bind_lookup_other source "nwd" "roots" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans roots)
    (bind_lookup_same source "nwd" (BitVec.ofNat 64 data.withdrawalCount))
    ((bind_lookup_other source "nwd" "i" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans position)
    ((bind_lookup_other source "nwd" "m2" (BitVec.ofNat 64 data.withdrawalCount) (by decide)).trans saved) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

theorem scope_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros oldRoots oldIndex : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word oldRoots)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word oldIndex)))
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word (chunksCursor ch))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source withdrawalScope=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [withdrawal_shapes.1] at run
  have read : eval source (fieldExpression 48)=some (.val (.word (data.withdrawals))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (48,data.withdrawals) (by simp [Description.cells])
  obtain ⟨inner,remaining,endpoint⟩ := ScalarScope.declare_trace source post "wd" (fieldExpression 48) (data.withdrawals) afterWd (some (.returned value)) read run
  have ready := actual.bind_current origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros "wd" (data.withdrawals) ⟨by decide,by decide,by decide,by decide,by decide⟩
  have checked := after_wd_normal data origin _ inner lower upper budget ch out mark stp accel chunk zeros oldRoots oldIndex image layout ready geometry outputGeometry separation small before
    ((bind_lookup_other source "wd" "roots" (data.withdrawals) (by decide)).trans roots)
    ((bind_lookup_other source "wd" "i" (data.withdrawals) (by decide)).trans position)
    ((bind_lookup_other source "wd" "m2" (data.withdrawals) (by decide)).trans saved)
    (bind_lookup_same source "wd" (data.withdrawals)) value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash.WithdrawalScope
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalScope.after_wd_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalScope.after_wd_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalScope.scope_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.WithdrawalScope.scope_normal

import InitECandidate.Solver.Input.PayloadHashBalance
import InitECandidate.Solver.Input.PayloadHashFinalPhase

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.FinalFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def afterBalance : ProgHOL 64 := StaticFields.program [.scalar 532 18] FinalPhase.afterScalar
def balanceSuffix : ProgHOL 64 := .seq BalancePhase.call afterBalance

theorem last_fits : ∀ field∈([.scalar 532 18] : List FixedHash.Step),field.Fits 540 19 1600 := by simp [FixedHash.Step.Fits,FixedHash.Step.inputOffset,FixedHash.Step.length,FixedHash.Step.field]
theorem front_fits : ∀ field∈([.scalar 512 15,.scalar 520 16] : List FixedHash.Step),field.Fits 540 19 1600 := by simp [FixedHash.Step.Fits,FixedHash.Step.inputOffset,FixedHash.Step.length,FixedHash.Step.field]

theorem after_balance_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterBalance=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤26416 := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have price := StaticFields.program_cost [.scalar 532 18] FinalPhase.afterScalar 26411 origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros last_fits fixed separation small before
    (fun current target ready observed evaluated notTimeout=>FinalPhase.after_scalar_cost data origin current target lower upper budget ch out mark stp accel chunk zeros layout ready geometry observed evaluated notTimeout)
    source post actual result run notTimeout
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,FixedHash.Step.price] at price
  omega

theorem after_balance_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterBalance=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have tail := fun current target ready returned evaluated=>FinalPhase.after_scalar_normal data origin current target lower upper budget ch out mark stp accel chunk zeros layout ready geometry outputGeometry separation small before returned evaluated
  exact ⟨StaticFields.program_return_heap [.scalar 532 18] FinalPhase.afterScalar origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros last_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).1) source post actual value run,
    StaticFields.program_frame [.scalar 532 18] FinalPhase.afterScalar origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros last_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).2) source post actual value run⟩

theorem balance_suffix_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source balanceSuffix=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤BalancePhase.price data+26416 := by
  exact ClockCost.sequence_terminating source post BalancePhase.call afterBalance (BalancePhase.price data) 26416
    (fun observed target evaluated notTimeout=>BalancePhase.call_cost data origin source target lower upper budget ch out mark stp accel chunk zeros image layout actual geometry observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have next:=BalancePhase.call_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation small before normal
        exact after_balance_cost data origin middle target lower upper budget ch out mark stp accel chunk zeros layout next geometry separation small before observed evaluated notTimeout)
    result run notTimeout

theorem balance_suffix_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source balanceSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have safe : LocalPrefix (ofString "raw") BalancePhase.call := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post BalancePhase.call afterBalance value (safe.summary_full source).2.1 run
  have next:=BalancePhase.call_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation small before normal
  exact after_balance_normal data origin middle post lower upper budget ch out mark stp accel chunk zeros layout next geometry outputGeometry separation small before value remaining

/-- Complete literal original payload tail after both shared-scope releases:
last scalar fields, actual balance byte hash, container and outer release. -/
theorem final_fields_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source finalFields=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤BalancePhase.price data+26426 := by
  rw [StaticFields.final_shape] at run
  change evaluateHOLFiniteState source (StaticFields.program [.scalar 512 15,.scalar 520 16] balanceSuffix)=(result,post) at run
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have price := StaticFields.program_cost [.scalar 512 15,.scalar 520 16] balanceSuffix (BalancePhase.price data+26416) origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros front_fits fixed separation small before
    (fun current target ready observed evaluated notTimeout=>balance_suffix_cost data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before observed evaluated notTimeout)
    source post actual result run notTimeout
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,FixedHash.Step.price] at price
  change source.clock-post.clock≤10+(BalancePhase.price data+26416) at price
  rw [Nat.add_left_comm 10 (BalancePhase.price data)] at price
  exact price

theorem final_fields_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source finalFields=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  rw [StaticFields.final_shape] at run
  change evaluateHOLFiniteState source (StaticFields.program [.scalar 512 15,.scalar 520 16] balanceSuffix)=(some (.returned value),post) at run
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have tail := fun current target ready returned evaluated=>balance_suffix_normal data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before returned evaluated
  exact ⟨StaticFields.program_return_heap [.scalar 512 15,.scalar 520 16] balanceSuffix origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros front_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).1) source post actual value run,
    StaticFields.program_frame [.scalar 512 15,.scalar 520 16] balanceSuffix origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros front_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).2) source post actual value run⟩

end InitECandidate.Solver.Input.PayloadHash.FinalFields

#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.last_fits
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.front_fits
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.after_balance_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.after_balance_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.balance_suffix_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.balance_suffix_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.final_fields_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalFields.final_fields_normal

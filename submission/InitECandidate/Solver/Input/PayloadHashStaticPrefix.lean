import InitECandidate.Solver.Input.PayloadHashTransactionScope
import InitECandidate.Solver.Input.PayloadHashExtra

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.StaticPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def middle : ProgHOL 64 := StaticFields.program StaticFields.middleFields transactionScope
def extraSuffix : ProgHOL 64 := .seq Extra.call middle
def middlePrice (data : Description) := 10+TransactionScope.price data
def extraSuffixPrice (data : Description) := Extra.price data+middlePrice data
def price (data : Description) := 1260+extraSuffixPrice data

theorem first_fits : ∀ field∈StaticFields.firstFields,field.Fits 540 19 1600 := by
  intro field member
  apply StaticFields.fields_fit field
  simp only [List.mem_append]; exact Or.inl (Or.inl member)

theorem middle_fits : ∀ field∈StaticFields.middleFields,field.Fits 540 19 1600 := by
  intro field member
  apply StaticFields.fields_fit field
  simp only [List.mem_append]; exact Or.inl (Or.inr member)

theorem middle_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source middle=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤middlePrice data := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have priced := StaticFields.program_cost StaticFields.middleFields transactionScope (TransactionScope.price data) origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros middle_fits fixed separation small before
    (fun current target ready observed evaluated notTimeout=>TransactionScope.scope_cost data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before observed evaluated notTimeout)
    source post actual result run notTimeout
  rw [StaticFields.field_prices.2.1] at priced
  exact priced

theorem middle_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source middle=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have tail := fun current target ready returned evaluated=>TransactionScope.scope_normal data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before returned evaluated
  exact ⟨StaticFields.program_return_heap StaticFields.middleFields transactionScope origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros middle_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).1) source post actual value run,
    StaticFields.program_frame StaticFields.middleFields transactionScope origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros middle_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).2) source post actual value run⟩

theorem extra_suffix_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source extraSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤extraSuffixPrice data := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  exact ClockCost.sequence_terminating source post Extra.call middle (Extra.price data) (middlePrice data)
    (fun observed target evaluated notTimeout=>Extra.call_cost data origin source target lower upper budget ch out (chunksCursor ch) mark stp accel chunk zeros image layout actual fixed observed evaluated notTimeout)
    (by intro current normal observed target evaluated notTimeout
        have next := Extra.call_normal data origin source current lower upper budget ch out (chunksCursor ch) mark stp accel chunk zeros image layout actual fixed separation small before normal
        exact middle_cost data origin current target lower upper budget ch out mark stp accel chunk zeros image layout next geometry separation small before observed evaluated notTimeout)
    result run notTimeout

theorem extra_suffix_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source extraSuffix=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have safe : LocalPrefix (ofString "raw") Extra.call := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨current,normal,remaining⟩ := sequence_returned source post Extra.call middle value (safe.summary_full source).2.1 run
  have next := Extra.call_normal data origin source current lower upper budget ch out (chunksCursor ch) mark stp accel chunk zeros image layout actual fixed separation small before normal
  exact middle_normal data origin current post lower upper budget ch out mark stp accel chunk zeros image layout next geometry outputGeometry separation small before value remaining

theorem after_chunks_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterChunks=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price data := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  rw [StaticFields.prefix_shape] at run
  change evaluateHOLFiniteState source (StaticFields.program StaticFields.firstFields extraSuffix)=(result,post) at run
  have priced := StaticFields.program_cost StaticFields.firstFields extraSuffix (extraSuffixPrice data) origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros first_fits fixed separation small before
    (fun current target ready observed evaluated notTimeout=>extra_suffix_cost data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry separation small before observed evaluated notTimeout)
    source post actual result run notTimeout
  rw [StaticFields.field_prices.1] at priced
  exact priced

theorem after_chunks_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterChunks=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  rw [StaticFields.prefix_shape] at run
  change evaluateHOLFiniteState source (StaticFields.program StaticFields.firstFields extraSuffix)=(some (.returned value),post) at run
  have tail := fun current target ready returned evaluated=>extra_suffix_normal data origin current target lower upper budget ch out mark stp accel chunk zeros image layout ready geometry outputGeometry separation small before returned evaluated
  exact ⟨StaticFields.program_return_heap StaticFields.firstFields extraSuffix origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros first_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).1) source post actual value run,
    StaticFields.program_frame StaticFields.firstFields extraSuffix origin lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros first_fits fixed separation small before
      (fun current target ready returned evaluated=>(tail current target ready returned evaluated).2) source post actual value run⟩

end InitECandidate.Solver.Input.PayloadHash.StaticPrefix
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.first_fits
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.middle_fits
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.middle_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.middle_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.extra_suffix_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.extra_suffix_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.after_chunks_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticPrefix.after_chunks_normal

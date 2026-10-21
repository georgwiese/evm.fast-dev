import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall
import InitECandidate.Solver.Input.PContainerGlobals
import InitECandidate.Solver.Input.HeapReleaseMemory

namespace InitECandidate.Solver.Input.PayloadHash.FinalPhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual caller output is mapped/aligned and follows the fixed decoded
input frontier. It may precede the callee's own temporary allocations. -/
structure OutputGeometry (out : BitVec 64) (upper : Nat) : Prop where
  arena : AllocatedBytes.Arena out 32
  aligned : out.toNat%8=0
  before : upper≤out.toNat

def containerCall : ProgHOL 64 := .call (some (none,none)) (ofString "htr_pcontainer") StaticFields.containerArguments
def afterScalar : ProgHOL 64 := .seq containerCall FixedHash.releaseSuffix

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.containerArguments=some (PContainer.values ch 19 out) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,StaticFields.containerArguments,localVar,chunks,output,PContainer.values]

theorem container_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source containerCall=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤26410 := by
  obtain ⟨fixed,scratch,number⟩ := data.static_geometry lower upper budget ch layout geometry
  have temporary := AllocatedBytes.Arena.weaken _ (data.scratchBytes budget) (896+64*19) scratch (by unfold Description.scratchBytes; omega)
  exact PContainer.call_cost source post ch (chunksCursor ch) out stp accel chunk zeros 19 (by decide) actual.ready.workspace actual.ready.heap fixed.chunksArena temporary fixed.aligned
    (some none) StaticFields.containerArguments (arguments_read source ch out actual.ready.chunks actual.ready.output) result run notTimeout

/-- Actual final original container hash retains the protected input region
and restores its current cursor before the real outer mark is released. -/
theorem container_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source containerCall=(none,post)) : StaticFields.State origin post lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros := by
  obtain ⟨fixed,scratch,number⟩ := data.static_geometry lower upper budget ch layout geometry
  have temporary := AllocatedBytes.Arena.weaken _ (data.scratchBytes budget) (896+64*19) scratch (by unfold Description.scratchBytes; omega)
  have args := arguments_read source ch out actual.ready.chunks actual.ready.output
  have heap := PContainer.ignored_return_heap source post ch (chunksCursor ch) out stp accel chunk zeros 19 (by decide) actual.ready.workspace actual.ready.heap fixed.chunksArena temporary fixed.aligned StaticFields.containerArguments args run
  apply actual.after_call origin source post lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros (ofString "htr_pcontainer") StaticFields.containerArguments run heap
  · intro key different
    exact GlobalEffects.call_body key source.code (some none) (ofString "htr_pcontainer") StaticFields.containerArguments PContainer.formals PContainer.body .one
      (PContainer.original_code source.code actual.ready.workspace.sha.installed) (PContainer.globals key source.code actual.ready.workspace.sha.installed different)
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have away := CopyGeneral.Away.after out query 32 outputGeometry.aligned (by have h:=outputGeometry.arena.upper; omega) (by have h:=outputGeometry.before; omega)
    exact PContainer.call_memory source post ch (chunksCursor ch) out stp accel chunk zeros query 19 (by decide) protection actual.ready.heap fixed.chunksArena temporary fixed.aligned
      (by rw [number]; omega) away StaticFields.containerArguments args run

/-- Real final container/outer-release suffix includes every non-timeout
outcome at26411source ticks. -/
theorem after_scalar_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterScalar=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤26411 := by
  have tail : ClockCost.Bound source.code FixedHash.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code actual.ready.workspace.sha.installed (some none) _) (ClockCost.returned source.code _)
  exact ClockCost.sequence_terminating source post containerCall FixedHash.releaseSuffix 26410 1
    (fun observed target evaluated notTimeout=>container_cost data origin source target lower upper budget ch out mark stp accel chunk zeros layout actual geometry observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have fields:=evaluation_fields source middle _ none normal
        have price:=tail middle fields.2.2.2
        rw [evaluated] at price
        exact price)
    result run notTimeout

/-- Normal final suffix derives actual saved-heap restoration and complete
input-region agreement through the same container/release/return execution. -/
theorem after_scalar_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterScalar=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  have safe : LocalPrefix (ofString "mark") containerCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post containerCall FixedHash.releaseSuffix value (safe.summary_full source).2.1 run
  have next := container_normal data origin source middle lower upper budget ch out mark stp accel chunk zeros layout actual geometry outputGeometry separation small before normal
  have heap := HeapScope.release_return_heap middle post mark (chunksCursor ch) next.ready.workspace.sha.installed next.ready.saved next.ready.heap value remaining
  refine ⟨heap,⟨?_⟩⟩
  intro query low high
  have memory := HeapScope.release_return_memory middle post [localVar "mark"] query next.ready.workspace.sha.installed value remaining
  exact memory.trans (next.input.words query low high)

end InitECandidate.Solver.Input.PayloadHash.FinalPhase

#print axioms InitECandidate.Solver.Input.PayloadHash.FinalPhase.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalPhase.container_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalPhase.container_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalPhase.after_scalar_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.FinalPhase.after_scalar_normal

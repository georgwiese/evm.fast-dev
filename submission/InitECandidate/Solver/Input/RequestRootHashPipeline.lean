import InitECandidate.Solver.Input.RequestRootHashPhaseMemory

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def pipelinePrice (data : Description) (phases : List Phase) := (phases.map (fun phase=>phase.price data)).sum+1

/-- Actual original phase pipeline plus its outer saved-mark release. Each
reached continuation receives the same proven current decoded-input image. -/
theorem pipeline_cost (phases : List Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (pipeline phases)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤pipelinePrice data phases := by
  induction phases generalizing source post result with
  | nil=>
    have priced := ClockCost.sequence source.code _ _ 1 0
      (HeapScope.release_call_cost source.code actual.workspace.sha.installed (some none) [localVar "mark"]) (ClockCost.returned source.code (.const 0#64)) source rfl
    change source.clock-(evaluateHOLFiniteState source (pipeline [])).2.clock≤1 at priced
    rw [run] at priced
    exact priced
  | cons phase rest ih=>
    change evaluateHOLFiniteState source (.seq phase.call (pipeline rest))=(result,post) at run
    have priced := ClockCost.sequence_terminating source post phase.call (pipeline rest) (phase.price data) (pipelinePrice data rest)
      (fun observed target evaluated notTimeout=>phase_cost phase data origin source target lower upper budget ch out mark stp accel chunk zeros image layout actual geometry outputGeometry.arena separation small before observed evaluated notTimeout)
      (by intro middle normal observed target evaluated notTimeout
          have next := phase_normal phase data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry outputGeometry separation small before normal
          exact ih middle target next observed evaluated notTimeout)
      result run notTimeout
    simpa only [pipelinePrice,List.map_cons,List.sum_cons,Nat.add_assoc] using priced

/-- Whole original pipeline normal return restores the genuine outer mark
and preserves the input and decoded records for later constructor phases. -/
theorem pipeline_normal (phases : List Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (pipeline phases)=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) ∧ HashInput.Frame origin post lower upper := by
  induction phases generalizing source post with
  | nil=>
    exact ⟨HeapScope.release_return_heap source post mark (cursor ch) actual.workspace.sha.installed actual.saved actual.heap value run,
      ⟨fun query low high=>(HeapScope.release_return_memory source post [localVar "mark"] query actual.workspace.sha.installed value run).trans (actual.input.words query low high)⟩⟩
  | cons phase rest ih=>
    change evaluateHOLFiniteState source (.seq phase.call (pipeline rest))=(some (.returned value),post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post phase.call (pipeline rest) value ((phase_local phase (ofString "si")).summary_full source).2.1 run
    have next := phase_normal phase data origin source middle lower upper budget ch out mark stp accel chunk zeros image layout actual geometry outputGeometry separation small before normal
    exact ih middle post next remaining

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.pipeline_cost
#print axioms InitECandidate.Solver.Input.RequestRootHash.pipeline_normal

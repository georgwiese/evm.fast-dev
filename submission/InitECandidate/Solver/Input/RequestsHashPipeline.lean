import InitECandidate.Solver.Input.RequestsHashStepNormal
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual five-field container call and original release/return suffix,
including all non-timeout failures in the observed continuation. -/
theorem after_lists_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterLists=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤24787 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) containerArguments=some (PContainer.values ch 5 out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,containerArguments,localVar,ready.chunks,ready.output,PContainer.values]
  have tempArena := AllocatedBytes.Arena.weaken cursor (96*capacity+1312) (896+64*5) geometry.temporaryArena (by omega)
  have releaseCost : ClockCost.Bound source.code FixedHash.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code ready.workspace.sha.installed (some none) _) (ClockCost.returned source.code _)
  exact ClockCost.sequence_terminating source post _ FixedHash.releaseSuffix 24786 1
    (by intro actual target evaluated notTimeout
        exact PContainer.call_cost source target ch cursor out stp accel chunk zeros 5 (by decide) ready.workspace ready.heap geometry.rootsArena tempArena geometry.aligned
          (some none) containerArguments args actual evaluated notTimeout)
    (by intro middle normal actual target evaluated notTimeout
        have fields:=evaluation_fields source middle _ none normal
        have price:=releaseCost middle fields.2.2.2
        rw [evaluated] at price
        exact price)
    result run notTimeout

def pipelinePrice (kinds : List Kind) (counts : Kind→Nat) :=
  (kinds.map (fun kind=>RequestListHash.price kind (counts kind)+1)).sum+24787

set_option maxRecDepth 4000 in
/-- Actual metadata preservation permits every reached original list call
to use the same decoded counts, charging each actual count only once. -/
theorem pipeline_cost (kinds : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (separation : Separation rq stp accel chunk)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (pipeline kinds)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤pipelinePrice kinds counts := by
  induction kinds generalizing source post result with
  | nil=>exact after_lists_cost source post rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry result run notTimeout
  | cons kind rest ih=>
    change evaluateHOLFiniteState source (.seq (step kind) (pipeline rest))=(result,post) at run
    have price := ClockCost.sequence_terminating source post _ _ (RequestListHash.price kind (counts kind)+1) (pipelinePrice rest counts)
      (by intro actual target evaluated notTimeout
          exact step_cost source target kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry actual evaluated notTimeout)
      (by intro middle normal actual target evaluated notTimeout
          have next:=step_normal source middle kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry separation normal
          exact ih middle target next actual evaluated notTimeout)
      result run notTimeout
    simpa only [pipelinePrice,List.map_cons,List.sum_cons,Nat.add_assoc] using price

/-- Evaluated original per-kind coefficients and one shared fixed overhead.
This is a source-clock bound, not a target certificate. -/
theorem pipeline_price (counts : Kind→Nat) : pipelinePrice RequestListHash.kinds counts=
    1827*counts .deposit+988*counts .wdreq+1364*counts .cons+1652*counts .bdep+813*counts .bexit+145842 := by
  have prices:=FixedHash.fixed_prices
  simp only [pipelinePrice,RequestListHash.kinds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,RequestListHash.price,RequestListHash.Kind.record]
  rw [prices.2.1,prices.2.2.1,prices.2.2.2.1,prices.2.2.2.2.1,prices.2.2.2.2.2]
  omega

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.after_lists_cost
#print axioms InitECandidate.Solver.Input.RequestsHash.pipeline_cost
#print axioms InitECandidate.Solver.Input.RequestsHash.pipeline_price

import InitECandidate.Solver.Input.CurrentHash.RequestsState
import InitECandidate.Solver.Input.CurrentHash.RequestsBudget
import InitECandidate.Solver.Input.CurrentHash.PContainerCost

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def pipelinePrice (kinds : List RequestList.Kind) (counts : Nat→BitVec 64) :=
  (kinds.map (fun kind=>RequestList.price kind (counts kind.tag).toNat+1)).sum

theorem tail_cost {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq ch cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : State input source blob rq ch cursor chunk out zeros start size counts) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterLists=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤3615 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "ch",.const 5#64,localVar "out"]=
      some [.val (.word ch),.val (.word 5#64),.val (.word out)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.chunks,data.output]
  unfold afterLists at actual
  exact ClockCost.sequence_terminating source post _ FixedRecord.releaseSuffix 3614 1
    (by intro observed target evaluated notTimeout
        exact PContainer.call_cost source target ch out 5 (by decide) data.context.installed (some none) _ args observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have release : ClockCost.Bound source.code FixedRecord.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
          (AllocatorCost.release_call source.code data.context.installed (some none) _) (ClockCost.returned source.code _)
        have price := release middle ((evaluation_fields source middle _ none normal).2.2.2)
        rw [evaluated] at price
        exact price) result actual notTimeout

/-- Compose the real five calls only after each actual normal call derives
its next complete decoded image. Failed calls stop within their own allowance. -/
theorem pipeline_cost (kinds : List RequestList.Kind) {input : Guest.InputBlob}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (blob rq ch cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : State input source blob rq ch cursor chunk out zeros start size counts) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (pipeline kinds afterLists)=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤pipelinePrice kinds counts+3615 := by
  induction kinds generalizing source post result with
  | nil=>exact tail_cost source post blob rq ch cursor chunk out zeros start size counts data result actual notTimeout
  | cons kind rest ih=>
    change evaluateHOLFiniteState source (.seq (listCall kind) (pipeline rest afterLists))=(result,post) at actual
    have args := arguments_read source blob rq ch start size counts kind data.decoded data.context.domain data.request data.chunks
    have total := ClockCost.sequence_terminating source post _ _ (RequestList.price kind (counts kind.tag).toNat+1) (pipelinePrice rest counts+3615)
      (by intro observed target evaluated notTimeout
          exact RequestList.call_cost source target kind (blob+BitVec.ofNat 64 start+Requests.offsetWord input start kind.tag)
            (ch+BitVec.ofNat 64 (32*kind.tag)) (counts kind.tag).toNat (data.decoded.count_bound kind.tag (kind_index kind)) data.context.installed
            (some none) (arguments kind) args observed evaluated notTimeout)
      (by intro middle normal observed target evaluated notTimeout
          exact ih middle target (data.after_list kind normal) observed evaluated notTimeout) result actual notTimeout
    simpa only [pipelinePrice,List.map_cons,List.sum_cons,Nat.add_assoc] using total

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.tail_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.pipeline_cost

import InitECandidate.Solver.Input.CurrentHash.RootStateCall

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}

def pipelinePrice (items : List Step) (input : Guest.InputBlob) (length start size : Nat) := (items.map (fun step=>step.price input length start size)).sum

theorem State.merkle_arguments (state : State input source blob si record rq root array ch cursor length start size) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) merkleArguments=some (Merkle.values ch 4#64 4#64 root) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,merkleArguments,localVar,state.chunks,state.data.out,Merkle.values]

theorem State.tail_cost (state : State input source blob si record rq root array ch cursor length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterLists=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤410 := by
  unfold afterLists at actual
  exact ClockCost.sequence_terminating source post _ releaseSuffix 409 1
    (by intro observed target evaluated noTimeout
        exact MerkleCallCost.cost source target ch 4#64 4#64 root 2 (by decide) (by decide) (by decide) state.data.workspace.code
          (some none) merkleArguments state.merkle_arguments observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have release : ClockCost.Bound source.code releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
          (AllocatorCost.release_call source.code state.data.workspace.code (some none) _) (ClockCost.returned source.code _)
        have paid:=release middle ((evaluation_fields source middle _ none normal).2.2.2)
        rw [evaluated] at paid
        exact paid) result actual notTimeout

/-- Compose the actual current root hash only after each real continuing
child call supplies its next complete same-decoder state and restored heap.
All observed non-timeout stopped prefixes remain in their own allowances. -/
theorem pipeline_cost (items : List Step) (state : State input source blob si record rq root array ch cursor length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (pipeline items afterLists)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤pipelinePrice items input length start size+410 := by
  induction items generalizing source post result with
  | nil=>exact state.tail_cost result actual notTimeout
  | cons item rest ih=>
    change evaluateHOLFiniteState source (.seq item.call (pipeline rest afterLists))=(result,post) at actual
    have paid := ClockCost.sequence_terminating source post item.call _ (item.price input length start size) (pipelinePrice rest input length start size+410)
      (by intro observed target evaluated noTimeout; exact state.call_cost (post:=target) item observed evaluated noTimeout)
      (by intro middle normal observed target evaluated noTimeout
          have next := state.after_call (post:=middle) item normal
          exact ih next observed evaluated noTimeout) result actual notTimeout
    simpa only [pipelinePrice,List.map_cons,List.sum_cons,Nat.add_assoc] using paid

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.merkle_arguments
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.tail_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.pipeline_cost

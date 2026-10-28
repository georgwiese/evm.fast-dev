import InitECandidate.Solver.Input.CurrentHash.RootMetadataGeometry

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def requestSize (input : Guest.InputBlob) := Guest.GasLimit.le32 input 6-16-Guest.GasLimit.le32 input 58

def Step.price (step : Step) (input : Guest.InputBlob) (length start size : Nat) := match step with
  | .payload=>PayloadHash.bodyPrice input length start size+1
  | .headers=>88*headerCount input+3169
  | .header=>42
  | .requests=>RequestsHash.bodyPrice (requestSize input)+1

/-- Every actual current root child call has its established allowance at
its same decoder-derived entry, including observed non-timeout stopping paths. -/
theorem State.call_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (step : Step)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source step.call=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤step.price input length start size := by
  have args := state.arguments_read step
  cases step with
  | payload=>
    have frontier:=state.payload_frontier
    exact PayloadHash.call_cost source post blob record array cursor WorkspaceEntry.chunkPointer ch WorkspaceEntry.zeroPointer length start size
      state.payload_context state.data.payload state.input_bounds.1 state.input_bounds.2.1 state.data.payloadArena state.data.payloadAligned frontier.1 frontier.2.1
      state.data.workspace.chunk state.data.workspace.chunkArena state.data.workspace.chunkAligned frontier.2.2 (some none) Step.payload.arguments args result actual notTimeout
  | headers=>
    exact PListCost.call_cost source post (headerPointer input blob) (BitVec.ofNat 64 (headerCount input)) (ch+32#64) (headerCount input)
      state.header_count_bound state.data.workspace.code (some none) Step.headers.arguments args result actual notTimeout
  | header=>
    have paid := FixedMemoryCost.copy source.code state.data.workspace.code (some none) (outputExpression 64) (field 24) 32 (by decide) source rfl
    change source.clock-(evaluateHOLFiniteState source Step.header.call).2.clock≤42 at paid
    rw [actual] at paid
    exact paid
  | requests=>
    obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
    have frontier:=state.requests_frontier
    have paid := RequestsHash.call_cost source post blob rq cursor WorkspaceEntry.chunkPointer (ch+96#64) WorkspaceEntry.zeroPointer requestStart requestSize counts
      state.requests_context requests frontier.1 state.data.workspace.chunk state.data.workspace.chunkArena state.data.workspace.chunkAligned frontier.2
      (some none) Step.requests.arguments args result actual notTimeout
    rw [requests.sizeEq] at paid
    exact paid

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.call_cost

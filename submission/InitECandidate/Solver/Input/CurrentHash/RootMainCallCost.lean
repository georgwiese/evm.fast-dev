import InitECandidate.Solver.Input.CurrentHash.RootCost

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's actual original root call receives the complete decoder/workspace
entry contract from its same decoder and real root allocation. This closes
the caller bound without supplying those obligations as extra hypotheses. -/
theorem main_call_cost {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(result,post))
    (notTimeout : result≠some .timeOut) : current.clock-post.clock≤bodyPrice input length start size+1 := by
  obtain ⟨callee,called,si,out⟩ := Invocation.environment current.code workspace.code origin.word root
  have data := Invocation.at_callee ready workspace callee si out
  exact ClockCost.call_current_terminating current post (some none) (ofString "htr_new_payload_request") RootEntry.arguments (Invocation.values origin.word root) body callee .one
    (bodyPrice input length start size) ready.args called
    (by intro observed target evaluated noTimeout; exact body_cost data observed evaluated noTimeout) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_call_cost

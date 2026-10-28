import InitECandidate.Solver.Input.CurrentVerify.MainEntry
import InitECandidate.Solver.Input.CurrentVerify.RunInputs

namespace InitECandidate.Solver.Input.CurrentVerify.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's actual root return and verification scope select the same physical
run_attempt input. Earlier stopped alternatives and the real later serializer
remain explicit; no independent successful helper run is substituted. -/
theorem root_trace {input : Guest.InputBlob} {decoded current hashed post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : CurrentHash.RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : CurrentHash.WorkspaceEntry.Workspace current)
    (rootRun : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") CurrentHash.RootEntry.arguments)=(none,hashed))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState hashed CurrentHash.HashPrefix.afterHash=(result,post)) :
    hashed.clock-post.clock≤1 ∨ ∃ entry target childResult,
      Data input entry origin.pointer origin.word record gasWord root.toNat ∧
      1≤hashed.clock ∧ entry.clock=hashed.clock-1 ∧ evaluateHOLFiniteState entry Verify.body=(childResult,target) ∧
      (entry.clock-target.clock≤8 ∨ ∃ runEntry runTarget runResult,
        Data input runEntry origin.pointer origin.word record gasWord root.toNat ∧
        LocalEffects.erase runEntry=LocalEffects.erase entry ∧ runEntry.clock=entry.clock-8 ∧
        evaluateHOLFiniteState runEntry RunAttempt.body=(runResult,runTarget) ∧ runTarget.clock=target.clock) ∧
      Resumes hashed target post childResult result := by
  have data:=main_inputs ready workspace rootRun
  rcases trace hashed post origin.word data.arena.code data.siLocal result actual with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨entry,target,childResult,funded,frame,clock,si,run,wrappers,remaining⟩ := observed
    have entryData:=data.of_frame frame si
    have next:=through_wrappers entryData childResult run
    exact Or.inr ⟨entry,target,childResult,entryData,funded,clock,run,next,remaining⟩

end InitECandidate.Solver.Input.CurrentVerify.Main

#print axioms InitECandidate.Solver.Input.CurrentVerify.Main.root_trace

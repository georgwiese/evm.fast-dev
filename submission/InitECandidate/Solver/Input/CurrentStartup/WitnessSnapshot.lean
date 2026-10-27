import InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The checked witness arrays at a particular physical post-state. A caller
must provide the exact nonlocal/clock frame to move this observation. -/
def Snapshot (input : Guest.InputBlob) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) : Prop :=
  ∃ headerSource ready headerPost, ∃ nodes codes headers : BitVec 64,
    ∃ nodeStart nodeLength codeStart codeLength start length : Nat,
      Result input headerSource ready headerPost pointer statelessRecord record gasWord requestRecord nodes codes headers
        payloadLength nodeStart nodeLength codeStart codeLength start length ∧
      LocalEffects.erase post = LocalEffects.erase headerPost ∧ post.clock = headerPost.clock

theorem Snapshot.of_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord : BitVec 64} {payloadLength : Nat}
    (actual : Snapshot input source pointer statelessRecord record gasWord requestRecord payloadLength)
    (frame : LocalEffects.erase target = LocalEffects.erase source) (clock : target.clock = source.clock) :
    Snapshot input target pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, beforeFrame, beforeClock⟩ := actual
  exact ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, frame.trans beforeFrame, clock.trans beforeClock⟩

end InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.of_frame

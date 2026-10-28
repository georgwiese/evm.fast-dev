import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.CurrentVerify.HeaderEntry

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- All real header entry arguments and records at the same exposed caller.
The actual run, result, lexical restoration and complete earlier input data
are retained even when header validation or a later phase stops. -/
theorem header_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body=(result,post)) :
    ∃ inner array start length,
      Data input (bind source "pl" record) pointer si record gasWord boundary ∧
      CurrentStartup.WitnessArrays.Image input (bind source "pl" record) pointer si array start length boundary 72 1024 256 ∧
      evaluateHOLFiniteState (bind source "pl" record) headerCall=(result,inner) ∧ post=restore source "pl" inner ∧
      evalListHOLFinite (bind source "pl" record) (h:=fun address=>Classical.propDecidable ((bind source "pl" record).memaddrs address)) headerArguments=
        some [.val (.word (VarList.decodedArray array length)),.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))] := by
  obtain ⟨inner,run,endpoint⟩ := header_entry source post si record data.arena.domain data.siArena data.siAligned data.siLocal data.payloadCell result actual
  have siNext:=(bind_lookup_other source "pl" "si" record (by decide)).trans data.siLocal
  have next:=data.of_frame (post:=bind source "pl" record) rfl siNext
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩ := data.witnesses
  have args:=header_arguments headerImage record data.arena.domain data.siLocal
  have image:=headerImage.of_interval (post:=bind source "pl" record) (by decide) (by intro query lower upper; rfl)
  exact ⟨inner,headers,headerStart,headerLength,next,image,run,endpoint,args⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_reached

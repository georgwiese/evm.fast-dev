import InitECandidate.Solver.Input.CurrentHash.RootReturned
import InitECandidate.Solver.Input.CurrentStartup.DecodedWitnessImages

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's actual normal root return carries all three original witness
arrays and six physical SI fields into stateless verification. Every image
comes from the same decoder, through the actual root allocation and hash call. -/
theorem main_witness_images {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    ∃ nodes codes headers : BitVec 64,∃ nodeStart nodeLength codeStart codeLength headerStart headerLength : Nat,
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word nodes nodeStart nodeLength root.toNat 40 1024 (2^31) ∧
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word codes codeStart codeLength root.toNat 56 65536 (2^31) ∧
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word headers headerStart headerLength root.toNat 72 1024 256 := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩ :=
    ready.snapshot.witness_images ready.enteringHeap
  have memory := main_earlier_memory ready workspace actual
  exact ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) memory,codeImage.of_interval (by decide) memory,headerImage.of_interval (by decide) memory⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_witness_images

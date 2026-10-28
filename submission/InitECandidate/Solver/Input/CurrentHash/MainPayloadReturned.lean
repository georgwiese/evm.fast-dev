import InitECandidate.Solver.Input.CurrentHash.RootReturned

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's actual root return keeps the physical SI payload pointer and
bounded payload gas cell, with both real allocated-record geometries. -/
theorem main_payload_cells {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    AllocatedBytes.Arena origin.word 96 ∧ origin.word.toNat%8=0 ∧ AllocatedBytes.Arena record 136 ∧ record.toNat%8=0 ∧
    post.memory origin.word=.word record ∧ post.memory (record+88#64)=.word gasWord ∧ gasWord.toNat≤200000000 := by
  have payloadCell:=ready.snapshot.payload_cell
  obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,
    headerStart,headerLength,data,frame,clock⟩ := ready.snapshot
  have memory:=LocalEffects.memory_of_erase headerPost decoded frame
  have siLower : 2701134640≤origin.word.toNat := by have a:=data.context.pointerLower; have b:=data.context.statelessLower; omega
  have recordLower : 2701134640≤record.toNat := by have h:=data.context.recordAfter; omega
  have siArena : AllocatedBytes.Arena origin.word 96 := ⟨by omega,by have h:=data.context.statelessRoom; omega⟩
  have recordArena : AllocatedBytes.Arena record 136 := ⟨by omega,by have h:=data.context.recordRoom; omega⟩
  have siFrame:=main_earlier_memory ready workspace actual origin.word siLower (by have a:=data.context.recordAfter; have b:=ready.rootAfter; omega)
  have gasNumber : (record+88#64).toNat=record.toNat+88 := byteAddress_toNat record 88 (by have h:=recordArena.upper; omega)
  have gasFrame:=main_earlier_memory ready workspace actual (record+88#64) (by rw [gasNumber]; omega)
    (by rw [gasNumber]; have h:=ready.rootAfter; omega)
  exact ⟨siArena,data.context.statelessAligned,recordArena,data.context.recordAligned,siFrame.trans payloadCell,
    gasFrame.trans ((congrFun memory _).trans data.gas),data.context.gasBound⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_payload_cells

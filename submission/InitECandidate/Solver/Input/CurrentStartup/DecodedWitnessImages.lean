import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayImage

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same final decoder snapshot supplies all three real witness arrays,
their six SI cells, per-item bounds and extents before its actual heap frontier. -/
theorem WitnessHeadersReturn.Snapshot.witness_images
    {origin : DecoderOrigin} {input : Guest.InputBlob} {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord rq frontier : BitVec 64} {payloadLength : Nat}
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin:=origin) input post pointer si record gasWord rq payloadLength)
    (heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word frontier))) :
    ∃ nodes codes headers : BitVec 64,∃ nodeStart nodeLength codeStart codeLength headerStart headerLength : Nat,
      WitnessArrays.Image input post pointer si nodes nodeStart nodeLength frontier.toNat 40 1024 (2^31) ∧
      WitnessArrays.Image input post pointer si codes codeStart codeLength frontier.toNat 56 65536 (2^31) ∧
      WitnessArrays.Image input post pointer si headers headerStart headerLength frontier.toNat 72 1024 256 := by
  obtain ⟨headerSource,ready,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,
    headerStart,headerLength,data,frame,clock⟩ := snapshot
  obtain ⟨codeSource,codeData⟩ := data.origin
  obtain ⟨nodeSource,nodePost,nodeData,nodeEndpoint⟩ := codeData.origin
  have memory:=LocalEffects.memory_of_erase headerPost post frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change post.globals=headerPost.globals at globals
  obtain ⟨cursor,cell,extent,bounded,aligned⟩ := data.heapExtent
  have cursorEq : cursor=frontier := by
    have same : some (.val (.word cursor) : ValueHOL 64)=some (.val (.word frontier)) := by
      rw [←cell,←globals]
      exact heap
    cases Option.some.inj same
    rfl
  subst cursor
  have readyDomain:=congrArg PanSemStateFiniteExact.memaddrs data.frame
  change headerPost.memaddrs=ready.memaddrs at readyDomain
  have domain : headerPost.memaddrs=InitE.ordinaryDomain := readyDomain.trans data.context.domain
  have siArena : AllocatedBytes.Arena si 96 := ⟨by have a:=data.context.pointerLower; have b:=data.context.statelessLower; omega,
    by have h:=data.context.statelessRoom; omega⟩
  have siLower : 2701134640≤si.toNat := by have a:=data.context.pointerLower; have b:=data.context.statelessLower; omega
  have siBefore : si.toNat+96≤frontier.toNat := by have a:=data.context.recordAfter; have b:=data.arrayAfter; omega
  have fields:=data.witness_fields
  have nodeCount : VarList.decodedCount input nodeStart nodeLength≤2^31 := by
    have h:=(VarList.Records.cells headerPost input pointer nodes nodeStart nodeLength domain data.nodeRecords).2.1
    omega
  have codeCount : VarList.decodedCount input codeStart codeLength≤2^31 := by
    have h:=(VarList.Records.cells headerPost input pointer codes codeStart codeLength domain data.codeRecords).2.1
    omega
  refine ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,?_,?_,?_⟩
  · exact ⟨siArena,data.context.statelessAligned,siLower,siBefore,data.context.pointerLower,nodeData.inside,
      by have h:=data.nodesBefore; omega,
      VarList.Records.of_memory headerPost post input pointer nodes nodeStart nodeLength memory data.nodeRecords,
      data.nodeLengths,nodeCount,(congrFun memory _).trans fields.1,(congrFun memory _).trans fields.2.1⟩
  · exact ⟨siArena,data.context.statelessAligned,siLower,siBefore,data.context.pointerLower,codeData.inside,
      by have h:=data.codesBefore; omega,
      VarList.Records.of_memory headerPost post input pointer codes codeStart codeLength memory data.codeRecords,
      data.codeLengths,codeCount,(congrFun memory _).trans fields.2.2.1,(congrFun memory _).trans fields.2.2.2.1⟩
  · exact ⟨siArena,data.context.statelessAligned,siLower,siBefore,data.context.pointerLower,data.inside,extent,
      VarList.Records.of_memory headerPost post input pointer headers headerStart headerLength memory data.headerRecords,
      data.headerLengths,data.headerCountBound,(congrFun memory _).trans fields.2.2.2.2.1,(congrFun memory _).trans fields.2.2.2.2.2⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.witness_images

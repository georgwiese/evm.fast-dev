import InitECandidate.Solver.Input.Witness.HeadersNormal

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The actual three-list decoder suffix establishes all witness records,
size/count checks, six SI fields and a shared linear allocation budget.
Validated witness offsets and the entry layout remain explicit premises. -/
theorem arrays_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start first middle last total : Nat)
    (environment : Environment source) (heap : Blob.HeapInput source input pointer)
    (ordered : first≤middle ∧ middle≤last ∧ last≤total) (inside : start+total≤input.length%2^64)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*total≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (firstLocal : source.locals.lookup (ofString "w0")=some (.val (.word (BitVec.ofNat 64 first))))
    (middleLocal : source.locals.lookup (ofString "w1")=some (.val (.word (BitVec.ofNat 64 middle))))
    (lastLocal : source.locals.lookup (ofString "w2")=some (.val (.word (BitVec.ofNat 64 last))))
    (totalLocal : source.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 total))))
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siAfter : pointer.toNat+input.length%2^64+8≤si.toNat)
    (siBefore : si.toNat+96≤array.toNat)
    (enough : 6*(input.length%2^64)+20≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source nodeCall=(some (.returned value),post)) :
    ∃ codeArray headerArray finalCursor : BitVec 64,
      value=.val (.word si) ∧
      VarList.Records post input pointer array (start+first) (middle-first) ∧
      VarList.Records post input pointer codeArray (start+middle) (last-middle) ∧
      VarList.Records post input pointer headerArray (start+last) (total-last) ∧
      (∀ index<VarList.decodedCount input (start+first) (middle-first),
        (VarList.recordLength input (start+first) (middle-first) (VarList.decodedCount input (start+first) (middle-first)) index).toNat≤1024) ∧
      (∀ index<VarList.decodedCount input (start+middle) (last-middle),
        (VarList.recordLength input (start+middle) (last-middle) (VarList.decodedCount input (start+middle) (last-middle)) index).toNat≤65536) ∧
      VarList.decodedCount input (start+last) (total-last)≤256 ∧ Blob.HeapInput post input pointer ∧
      post.memory (byteAddress si 40)=.word (VarList.decodedArray array (middle-first)) ∧
      post.memory (byteAddress si 48)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+first) (middle-first))) ∧
      post.memory (byteAddress si 56)=.word (VarList.decodedArray codeArray (last-middle)) ∧
      post.memory (byteAddress si 64)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+middle) (last-middle))) ∧
      post.memory (byteAddress si 72)=.word (VarList.decodedArray headerArray (total-last)) ∧
      post.memory (byteAddress si 80)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+last) (total-last))) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalCursor)) ∧
      codeArray.toNat=array.toNat+16*VarList.decodedCount input (start+first) (middle-first) ∧
      headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (start+middle) (last-middle) ∧
      codeArray.toNat%8=0 ∧ headerArray.toNat%8=0 ∧
      finalCursor.toNat=array.toNat+16*(VarList.decodedCount input (start+first) (middle-first)+
        VarList.decodedCount input (start+middle) (last-middle)+VarList.decodedCount input (start+last) (total-last)) ∧
      finalCursor.toNat≤array.toNat+4*total ∧ finalCursor.toNat%8=0 ∧
      source.clock-(6*(input.length%2^64)+9)≤post.clock ∧ post.clock≤source.clock := by
  classical
  have bytesSmall : input.length%2^64<2^64:=Nat.mod_lt _ (by decide)
  have firstArgs:=list_arguments source pointer start first middle 9223372036854775807 1024 "w0" "w1"
    ordered.1 (by omega) wp firstLocal middleLocal
  rw [arrays_shape.1,arrays_shape.2.1] at run
  obtain ⟨nodeNext,nodeInner,nodeLocals,nodes,nodeLimit,nodeSizes,nodeHeap,nodePointer,nodeCount,nodeCursor,
      nodeLower,nodeUpper,nodeFrame,nodeControl,nodeRest,nodePost⟩:=stored_list_normal source post input pointer array
    9223372036854775807#64 1024#64 si (start+first) (middle-first) 40 heap (by omega)
    environment.domain lower aligned arrayAligned arrayAfter (by omega) heapGlobal
    environment.allocCode environment.failCode environment.exceptionShape environment.varCode environment.code
    siLocal siArena siAligned siAfter siBefore (by decide) (by decide) "st0" (by decide)
    (listArguments "w0" "w1" 9223372036854775807 1024) codeCall firstArgs (by omega) value run
  have nodeEnvironment:=Environment.after_list source nodeNext array _ (middle-first=0) nodeControl environment
  have nodeCountBound:=(VarList.Records.cells nodeNext input pointer array (start+first) (middle-first) nodeEnvironment.domain nodes).1
  let codeArray:=VarList.nextCursor array (VarList.decodedCount input (start+first) (middle-first))
  have codeGeometry:=VarList.nextCursor_geometry array (VarList.decodedCount input (start+first) (middle-first)) arrayAligned (by omega)
  have codeNumber : codeArray.toNat=array.toNat+16*VarList.decodedCount input (start+first) (middle-first):=codeGeometry.1
  have nodeSi:=local_after_tuple source nodeNext "st0" "si" _ _ (by decide) nodeLocals siLocal
  have nodeWp:=local_after_tuple source nodeNext "st0" "wp" _ _ (by decide) nodeLocals wp
  have nodeMiddle:=local_after_tuple source nodeNext "st0" "w1" _ _ (by decide) nodeLocals middleLocal
  have nodeLast:=local_after_tuple source nodeNext "st0" "w2" _ _ (by decide) nodeLocals lastLocal
  have nodeTotal:=local_after_tuple source nodeNext "st0" "wlen" _ _ (by decide) nodeLocals totalLocal
  have codeArgs:=list_arguments nodeNext pointer start middle last 9223372036854775807 65536 "w1" "w2"
    ordered.2.1 (by omega) nodeWp nodeMiddle nodeLast
  rw [arrays_shape.2.2.1,arrays_shape.2.2.2.1] at nodeRest
  obtain ⟨codeNext,codeInner,codeLocals,codes,codeLimit,codeSizes,codeHeap,codePointer,codeCount,codeCursor,
      codeLower,codeUpper,codeFrame,codeControl,codeRest,codePost⟩:=stored_list_normal nodeNext nodeInner input pointer codeArray
    9223372036854775807#64 65536#64 si (start+middle) (last-middle) 56 nodeHeap (by omega)
    nodeEnvironment.domain lower aligned codeGeometry.2.1 (by rw [codeNumber];omega) (by rw [codeNumber];omega) nodeCursor
    nodeEnvironment.allocCode nodeEnvironment.failCode nodeEnvironment.exceptionShape nodeEnvironment.varCode nodeEnvironment.code
    nodeSi siArena siAligned siAfter (by rw [codeNumber];omega) (by decide) (by decide) "cd" (by decide)
    (listArguments "w1" "w2" 9223372036854775807 65536) headerCall codeArgs (by omega) value nodeRest
  have codeEnvironment:=Environment.after_list nodeNext codeNext codeArray _ (last-middle=0) codeControl nodeEnvironment
  have codeCountBound:=(VarList.Records.cells codeNext input pointer codeArray (start+middle) (last-middle) codeEnvironment.domain codes).1
  let headerArray:=VarList.nextCursor codeArray (VarList.decodedCount input (start+middle) (last-middle))
  have headerGeometry:=VarList.nextCursor_geometry codeArray (VarList.decodedCount input (start+middle) (last-middle)) codeGeometry.2.1 (by rw [codeNumber];omega)
  have headerNumber : headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (start+middle) (last-middle):=headerGeometry.1
  have codeSi:=local_after_tuple nodeNext codeNext "cd" "si" _ _ (by decide) codeLocals nodeSi
  have codeWp:=local_after_tuple nodeNext codeNext "cd" "wp" _ _ (by decide) codeLocals nodeWp
  have codeLast:=local_after_tuple nodeNext codeNext "cd" "w2" _ _ (by decide) codeLocals nodeLast
  have codeTotal:=local_after_tuple nodeNext codeNext "cd" "wlen" _ _ (by decide) codeLocals nodeTotal
  obtain ⟨valueEq,headers,headerLimit,headerSizes,headerHeap,headerPointer,headerCount,headerCursor,
      headerLower,headerUpper,headerFrame,headerControl⟩:=headers_normal codeNext codeInner input pointer headerArray si start last total
    codeEnvironment codeHeap ordered.2.2 inside lower aligned headerGeometry.2.1
    (by rw [headerNumber,codeNumber];omega) (by rw [headerNumber,codeNumber];omega) codeCursor
    codeWp codeLast codeTotal codeSi siArena siAligned siAfter (by rw [headerNumber,codeNumber];omega) (by omega) value codeRest
  have headerEnvironment:=Environment.after_list codeNext codeInner headerArray _ (total-last=0) headerControl codeEnvironment
  have headerCountBound:=(VarList.Records.cells codeInner input pointer headerArray (start+last) (total-last) headerEnvironment.domain headers).1
  let finalCursor:=VarList.nextCursor headerArray (VarList.decodedCount input (start+last) (total-last))
  have finalGeometry:=VarList.nextCursor_geometry headerArray (VarList.decodedCount input (start+last) (total-last)) headerGeometry.2.1
    (by rw [headerNumber,codeNumber];omega)
  have finalNumber : finalCursor.toNat=headerArray.toNat+16*VarList.decodedCount input (start+last) (total-last):=finalGeometry.1
  have nodesAfterCode:=records_through_list nodeNext codeNext input pointer array si (start+first) (middle-first) codeArray.toNat 56 nodes
    (by rw [codeNumber]) siArena siBefore (by decide) codeFrame
  have nodesAfterHeaders:=records_through_list codeNext codeInner input pointer array si (start+first) (middle-first) headerArray.toNat 72 nodesAfterCode
    (by rw [headerNumber,codeNumber];omega) siArena siBefore (by decide) headerFrame
  have codesAfterHeaders:=records_through_list codeNext codeInner input pointer codeArray si (start+middle) (last-middle) headerArray.toNat 72 codes
    (by rw [headerNumber]) siArena (by rw [codeNumber];omega) (by decide) headerFrame
  have nodePointerAfterCode:=field_through_list nodeNext codeNext si codeArray.toNat 40 56 _ siArena (by rw [codeNumber];omega)
    (by decide) (by decide) (by decide) nodePointer codeFrame
  have nodeCountAfterCode:=field_through_list nodeNext codeNext si codeArray.toNat 48 56 _ siArena (by rw [codeNumber];omega)
    (by decide) (by decide) (by decide) nodeCount codeFrame
  have nodePointerFinal:=field_through_list codeNext codeInner si headerArray.toNat 40 72 _ siArena (by rw [headerNumber,codeNumber];omega)
    (by decide) (by decide) (by decide) nodePointerAfterCode headerFrame
  have nodeCountFinal:=field_through_list codeNext codeInner si headerArray.toNat 48 72 _ siArena (by rw [headerNumber,codeNumber];omega)
    (by decide) (by decide) (by decide) nodeCountAfterCode headerFrame
  have codePointerFinal:=field_through_list codeNext codeInner si headerArray.toNat 56 72 _ siArena (by rw [headerNumber,codeNumber];omega)
    (by decide) (by decide) (by decide) codePointer headerFrame
  have codeCountFinal:=field_through_list codeNext codeInner si headerArray.toNat 64 72 _ siArena (by rw [headerNumber,codeNumber];omega)
    (by decide) (by decide) (by decide) codeCount headerFrame
  have postMemory : post.memory=codeInner.memory := by rw [nodePost,codePost];rfl
  have postGlobals : post.globals=codeInner.globals := by rw [nodePost,codePost];rfl
  have postClock : post.clock=codeInner.clock := by rw [nodePost,codePost];rfl
  have postDomain : codeInner.memaddrs=post.memaddrs := by rw [nodePost,codePost];rfl
  have postEndian : codeInner.be=post.be := by rw [nodePost,codePost];rfl
  refine ⟨codeArray,headerArray,finalCursor,valueEq,
    VarList.Records.of_memory codeInner post input pointer array (start+first) (middle-first) postMemory nodesAfterHeaders,
    VarList.Records.of_memory codeInner post input pointer codeArray (start+middle) (last-middle) postMemory codesAfterHeaders,
    VarList.Records.of_memory codeInner post input pointer headerArray (start+last) (total-last) postMemory headers,
    nodeSizes,codeSizes,headerLimit,Blob.HeapInput.of_fields codeInner post input pointer postMemory.symm postDomain postEndian headerHeap,
    ?_,?_,?_,?_,?_,?_,?_,codeNumber,headerNumber,codeGeometry.2.1,headerGeometry.2.1,?_,?_,finalGeometry.2.1,?_,?_⟩
  · rw [postMemory];exact nodePointerFinal
  · rw [postMemory];exact nodeCountFinal
  · rw [postMemory];exact codePointerFinal
  · rw [postMemory];exact codeCountFinal
  · rw [postMemory];exact headerPointer
  · rw [postMemory];exact headerCount
  · rw [postGlobals];exact headerCursor
  · rw [finalNumber,headerNumber,codeNumber];omega
  · rw [finalNumber,headerNumber,codeNumber];omega
  · rw [postClock];omega
  · rw [postClock];omega

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.arrays_normal

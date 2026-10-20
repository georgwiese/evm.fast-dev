import InitECandidate.Solver.Input.Witness.HeadersTrace

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The three original witness byte-list calls and all SI stores/return on
every non-timeout outcome. All branches share the same encoded byte budget;
no malformed-record or oversize-record path assumes a future normal return. -/
theorem arrays_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source nodeCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(total-first)/2+12 ∧
      ((∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word si)))) := by
  classical
  have bytesSmall : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
  have firstArgs := list_arguments source pointer start first middle 9223372036854775807 1024 "w0" "w1" ordered.1 (by omega) wp firstLocal middleLocal
  rw [arrays_shape.1,arrays_shape.2.1] at run
  rcases stored_list_trace source post input pointer array 9223372036854775807#64 1024#64 si (start+first) (middle-first) 40 heap (by omega)
    environment.domain lower aligned arrayAligned arrayAfter (by omega) heapGlobal environment.allocCode environment.failCode environment.exceptionShape environment.varCode environment.code
    siLocal siArena siAligned siAfter siBefore (by decide) (by decide) "st0" (by decide) (listArguments "w0" "w1" 9223372036854775807 1024) codeCall firstArgs result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,allowed,same⟩⟩
  obtain ⟨nodeNext,nodeInner,nodeLocals,nodes,nodeLimit,nodeSizes,nodeHeap,nodePointer,nodeCount,nodeCursor,nodeCost,nodeForward,nodeFrame,nodeControl,nodeRest,nodePost⟩ := normal
  have nodeEnvironment := Environment.after_list source nodeNext array _ (middle-first=0) nodeControl environment
  have nodeCountBound := (VarList.Records.cells nodeNext input pointer array (start+first) (middle-first) nodeEnvironment.domain nodes).1
  let codeArray := VarList.nextCursor array (VarList.decodedCount input (start+first) (middle-first))
  have codeGeometry := VarList.nextCursor_geometry array (VarList.decodedCount input (start+first) (middle-first)) arrayAligned (by omega)
  have codeNumber : codeArray.toNat=array.toNat+16*VarList.decodedCount input (start+first) (middle-first) := codeGeometry.1
  have nodeSi := local_after_tuple source nodeNext "st0" "si" _ _ (by decide) nodeLocals siLocal
  have nodeWp := local_after_tuple source nodeNext "st0" "wp" _ _ (by decide) nodeLocals wp
  have nodeMiddle := local_after_tuple source nodeNext "st0" "w1" _ _ (by decide) nodeLocals middleLocal
  have nodeLast := local_after_tuple source nodeNext "st0" "w2" _ _ (by decide) nodeLocals lastLocal
  have nodeTotal := local_after_tuple source nodeNext "st0" "wlen" _ _ (by decide) nodeLocals totalLocal
  have codeArgs := list_arguments nodeNext pointer start middle last 9223372036854775807 65536 "w1" "w2" ordered.2.1 (by omega) nodeWp nodeMiddle nodeLast
  have nodeSuffixForward := evaluateHOLFiniteState_clock_le nodeNext codeCall
  rw [nodeRest] at nodeSuffixForward
  change nodeInner.clock≤nodeNext.clock at nodeSuffixForward
  rw [arrays_shape.2.2.1,arrays_shape.2.2.2.1] at nodeRest
  rcases stored_list_trace nodeNext nodeInner input pointer codeArray 9223372036854775807#64 65536#64 si (start+middle) (last-middle) 56 nodeHeap (by omega)
    nodeEnvironment.domain lower aligned codeGeometry.2.1 (by rw [codeNumber]; omega) (by rw [codeNumber]; omega) nodeCursor
    nodeEnvironment.allocCode nodeEnvironment.failCode nodeEnvironment.exceptionShape nodeEnvironment.varCode nodeEnvironment.code
    nodeSi siArena siAligned siAfter (by rw [codeNumber]; omega) (by decide) (by decide) "cd" (by decide)
    (listArguments "w1" "w2" 9223372036854775807 65536) headerCall codeArgs result nodeRest notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have endpoint : post.clock=nodeInner.clock := by rw [nodePost]; rfl
    exact ⟨by rw [endpoint]; omega,Or.inl ⟨error,allowed,same⟩⟩
  obtain ⟨codeNext,codeInner,codeLocals,codes,codeLimit,codeSizes,codeHeap,codePointer,codeCount,codeCursor,codeCost,codeForward,codeFrame,codeControl,codeRest,codePost⟩ := normal
  have codeEnvironment := Environment.after_list nodeNext codeNext codeArray _ (last-middle=0) codeControl nodeEnvironment
  have codeCountBound := (VarList.Records.cells codeNext input pointer codeArray (start+middle) (last-middle) codeEnvironment.domain codes).1
  let headerArray := VarList.nextCursor codeArray (VarList.decodedCount input (start+middle) (last-middle))
  have headerGeometry := VarList.nextCursor_geometry codeArray (VarList.decodedCount input (start+middle) (last-middle)) codeGeometry.2.1 (by rw [codeNumber]; omega)
  have headerNumber : headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (start+middle) (last-middle) := headerGeometry.1
  have codeSi := local_after_tuple nodeNext codeNext "cd" "si" _ _ (by decide) codeLocals nodeSi
  have codeWp := local_after_tuple nodeNext codeNext "cd" "wp" _ _ (by decide) codeLocals nodeWp
  have codeLast := local_after_tuple nodeNext codeNext "cd" "w2" _ _ (by decide) codeLocals nodeLast
  have codeTotal := local_after_tuple nodeNext codeNext "cd" "wlen" _ _ (by decide) codeLocals nodeTotal
  obtain ⟨headerCost,outcome⟩ := headers_trace codeNext codeInner input pointer headerArray si start last total codeEnvironment codeHeap ordered.2.2 inside lower aligned headerGeometry.2.1
    (by rw [headerNumber,codeNumber]; omega) (by rw [headerNumber,codeNumber]; omega) codeCursor codeWp codeLast codeTotal codeSi siArena siAligned siAfter (by rw [headerNumber,codeNumber]; omega) result codeRest notTimeout
  have headerForward := evaluateHOLFiniteState_clock_le codeNext headerCall
  rw [codeRest] at headerForward
  change codeInner.clock≤codeNext.clock at headerForward
  have endpoint : post.clock=codeInner.clock := by rw [nodePost,codePost]; rfl
  exact ⟨by rw [endpoint]; omega,outcome⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.arrays_trace

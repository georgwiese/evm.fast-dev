import InitECandidate.Solver.Input.CurrentHash.Invocation

namespace InitECandidate.Solver.Input.CurrentHash.Invocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array : BitVec 64} {length start size : Nat}

/-- Pure root scope entries retain the same decoder data directly. -/
theorem Data.of_frame (data : Data input source blob si record rq root array length start size)
    (frame : LocalEffects.erase post=LocalEffects.erase source)
    (siLocal : post.locals.lookup (ofString "si")=some (.val (.word si))) (outLocal : post.locals.lookup (ofString "out")=some (.val (.word root))) :
    Data input post blob si record rq root array length start size := by
  have code := congrArg PanSemStateFiniteExact.code frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  have endian := congrArg PanSemStateFiniteExact.be frame
  have memory := LocalEffects.memory_of_erase source post frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change post.code=source.code at code
  change post.memaddrs=source.memaddrs at domain
  change post.be=source.be at endian
  change post.globals=source.globals at globals
  have installed : OriginalCode.Installed post.code := by rw [code]; exact data.workspace.code
  have cell (name : String) : post.globals.lookup (ofString name)=source.globals.lookup (ofString name) := congrArg (fun table=>table.lookup (ofString name)) globals
  have workspace : WorkspaceEntry.Workspace post := ⟨installed,domain.trans data.workspace.domain,endian.trans data.workspace.little,
    (cell "ssz_offs").trans data.workspace.offsets,(cell "ssz_len_chunk").trans data.workspace.chunk,(cell "zero_hashes").trans data.workspace.zeros,
    (cell "keccak_st").trans data.workspace.keccakState,(cell "keccak_pad").trans data.workspace.keccakPad,(cell "mpt_hash_scratch").trans data.workspace.mptHash,(cell "mpt_key_scratch").trans data.workspace.mptKey,
    data.workspace.chunkArena,data.workspace.zeroArena,data.workspace.chunkAligned,data.workspace.zeroAligned⟩
  have arena : CurrentStartup.ArenaState post := ⟨(cell "scratch_ptr").trans data.arena.scratch,(cell "frame_mem_ptr").trans data.arena.frame,workspace.domain,installed⟩
  obtain ⟨cursor,heap,lower,bounded,aligned⟩ := data.heap
  have nextHeap : NormalHeapEffects.AtLeast (root.toNat+32) post := ⟨cursor,(cell "heap_ptr").trans heap,lower,bounded,aligned⟩
  obtain ⟨requestStart,requestSize,counts,requests⟩ := data.requestImage
  have requestImage : Requests.DecodedImage input post blob rq requestStart requestSize counts := requests.of_memory (by intro index inside; exact ⟨congrFun memory _,congrFun memory _⟩)
  exact ⟨workspace,arena,data.payload.of_frame frame,nextHeap,siLocal,outLocal,data.siArena,data.siAligned,data.rootArena,data.rootAligned,
    data.payloadArena,data.payloadAligned,data.payloadAfterSI,data.siAfterInput,data.rootAfter,data.arrayBefore,(congrFun memory _).trans data.payloadCell,
    (congrFun memory _).trans data.hashPointer,(congrFun memory _).trans data.hashCount,(congrFun memory _).trans data.header,(congrFun memory _).trans data.requests,
    requestStart,requestSize,counts,requestImage⟩

theorem Data.at_clock (data : Data input source blob si record rq root array length start size) (clock : Nat) : Data input {source with clock:=clock} blob si record rq root array length start size :=
  data.of_frame rfl data.si data.out

theorem Data.bound (data : Data input source blob si record rq root array length start size) (name : String) (word : BitVec 64)
    (different : ofString name≠ofString "si" ∧ ofString name≠ofString "out") : Data input (bind source name word) blob si record rq root array length start size :=
  data.of_frame rfl ((bind_lookup_other source name "si" word different.1).trans data.si) ((bind_lookup_other source name "out" word different.2).trans data.out)

/-- Transfer the same complete decoder images through a real root prefix.
Only actual earlier SI/payload/RQ metadata and the current heap are retained;
input/digest contents and unrelated executions are not hypotheses. -/
theorem Data.of_interval (data : Data input source blob si record rq root array length start size)
    (workspace : WorkspaceEntry.Workspace post) (arena : CurrentStartup.ArenaState post) (heap : NormalHeapEffects.AtLeast (root.toNat+32) post)
    (siLocal : post.locals.lookup (ofString "si")=some (.val (.word si))) (outLocal : post.locals.lookup (ofString "out")=some (.val (.word root)))
    (boundary : Nat) (afterRoot : root.toNat+32≤boundary)
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat → query.toNat<boundary → post.memory query=source.memory query) :
    Data input post blob si record rq root array length start size := by
  obtain ⟨requestStart,requestSize,counts,requests⟩ := data.requestImage
  have siLower : 2701134824≤si.toNat := by have a:=requests.inputLower; have b:=data.siAfterInput; omega
  have recordLower : 2701134824≤record.toNat := by have h:=data.payloadAfterSI; omega
  have siFrame (offset : Nat) (inside : offset<96) : post.memory (si+BitVec.ofNat 64 offset)=source.memory (si+BitVec.ofNat 64 offset) := by
    have number : (si+BitVec.ofNat 64 offset).toNat=si.toNat+offset := byteAddress_toNat si offset (by have h:=data.siArena.upper; omega)
    apply memory
    · rw [number]; omega
    · rw [number]; have a:=data.payloadAfterSI; have b:=data.rootAfter; omega
  have requestFrame (offset : Nat) (inside : offset<80) : post.memory (rq+BitVec.ofNat 64 offset)=source.memory (rq+BitVec.ofNat 64 offset) := by
    have number : (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset := byteAddress_toNat rq offset (by have h:=requests.cursorRoom; omega)
    apply memory
    · rw [number]; have a:=requests.inputLower; have b:=requests.cursorAfterInput; omega
    · rw [number]; have h:=data.rootAfter; omega
  have requestImage : Requests.DecodedImage input post blob rq requestStart requestSize counts := requests.of_memory
    (by intro index inside; exact ⟨requestFrame (16*index) (by omega),requestFrame (16*index+8) (by omega)⟩)
  obtain ⟨cursor,heapCell,heapLower,heapBound,heapAligned⟩ := heap
  have arrayHeap : NormalHeapEffects.AtLeast (array.toNat+16*VarList.decodedCount input start size) post :=
    ⟨cursor,heapCell,by have h:=data.arrayBefore; omega,heapBound,heapAligned⟩
  have payload := data.payload.of_interval boundary (by have h:=data.arrayBefore; omega)
    (by intro query lower upper; exact memory query (by omega) upper) arrayHeap
  have siZero : post.memory si=source.memory si := by simpa only [BitVec.add_zero] using siFrame 0 (by decide)
  exact ⟨workspace,arena,payload,⟨cursor,heapCell,heapLower,heapBound,heapAligned⟩,siLocal,outLocal,data.siArena,data.siAligned,data.rootArena,data.rootAligned,
    data.payloadArena,data.payloadAligned,data.payloadAfterSI,data.siAfterInput,data.rootAfter,data.arrayBefore,siZero.trans data.payloadCell,
    (siFrame 8 (by decide)).trans data.hashPointer,(siFrame 16 (by decide)).trans data.hashCount,(siFrame 24 (by decide)).trans data.header,
    (siFrame 32 (by decide)).trans data.requests,requestStart,requestSize,counts,requestImage⟩

end InitECandidate.Solver.Input.CurrentHash.Invocation

#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.Data.of_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.Data.bound
#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.Data.of_interval

import InitECandidate.Solver.Input.CurrentVerify.Withdrawals

namespace InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

def body : ProgHOL 64:=match Guest.Software.guestFn_encode_execution_requests with | .function fn=>progToHOL fn.body | _=>.skip
abbrev resultShape : ShapeHOL:=.comb [.one,.one]
def arguments : List (ExpHOL 64):=[.load .one (Scalar.plus (localVar "si") 32)]

def afterEncode : ProgHOL 64:=match PayloadHeaderWithdrawals.afterRoot with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem caller_shape : PayloadHeaderWithdrawals.afterRoot=
    .decCall (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments afterEncode := by
  simp only [afterEncode,PayloadHeaderWithdrawals.afterRoot,afterLoop,loopAndAfter,afterArray,afterCount,
    afterTransactionTrie,afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,arguments,resultShape,Scalar.plus,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "encode_execution_requests")=some ([(ofString "rq",.one)],body,resultShape) := by
  have checked:=OriginalCode.indexed code installed 780 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_encode_execution_requests) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,resultShape,
    Guest.Software.guestFn_encode_execution_requests,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

/-- The actual accepted lists share their encoded byte budget. No independent
maximum count, future allocation room or successful hash is supplied. -/
theorem list_bytes {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (image : Requests.DecodedImage input source pointer rq start size counts) (index : Nat) (inside : index<5) :
    (counts index).toNat*(Requests.elementSize index).toNat≤size-20 ∧ size≤251655056 := by
  have budget:=image.byte_budget
  have sizeBound : size≤251655056:=by have bytes:=image.inputBound; have extent:=image.inside; omega
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;>
    simp only [Requests.elementSize,BitVec.toNat_ofNat] <;> omega

/-- The multiplication used by the original allocation/copy never wraps
for a list supplied by this actual decoder. -/
theorem list_size_number {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (image : Requests.DecodedImage input source pointer rq start size counts) (index : Nat) (inside : index<5) :
    (counts index*Requests.elementSize index).toNat=(counts index).toNat*(Requests.elementSize index).toNat := by
  rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by have bytes:=list_bytes image index inside; omega)]

/-- Request hashing reads the exact same RQ pointer retained through the
actual transaction and withdrawal tries. -/
theorem arguments_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    ∃ rq start size counts,
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word rq)] ∧
      Requests.DecodedImage input source pointer rq start size counts ∧ rq.toNat+80≤boundary := by
  obtain ⟨rq,start,size,counts,cell,image,before⟩:=data.requests
  have read:=Witness.load_word_read source (Scalar.plus (localVar "si") 32) (si+32#64) rq
    (Scalar.plus_read source (localVar "si") si 32 (PayloadHeaderEntry.local_word_read source "si" si data.siLocal))
    (AllocatedBytes.word_mapped source si 96 32 data.arena.domain data.siArena (by decide) data.siAligned (by decide)) cell
  refine ⟨rq,start,size,counts,?_,image,before⟩
  simp only [eval] at read
  simp only [arguments,evalListHOLFinite,evalListHOLExact,read]

/-- Only facts already reached at this callee entry: its real RQ ABI,
initialized hash/global environment, copied request records and incoming heap. -/
structure Entry (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer rq heap : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  image : Requests.DecodedImage input source pointer rq start size counts
  request : source.locals.lookup (ofString "rq")=some (.val (.word rq))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : rq.toNat+80≤heap.toNat
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0

/-- The literal main caller supplies the true request encoder entry and
word ABI. Neither its return nor the following hash is assumed. -/
theorem main_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    ∃ rq heap start size counts callee,
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word rq)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "encode_execution_requests") [.val (.word rq)]=some (body,callee,resultShape) ∧
      Entry input (callEntryStateHOLFinite source callee) pointer rq heap start size counts := by
  obtain ⟨rq,start,size,counts,args,image,before⟩:=arguments_read data
  obtain ⟨callee,called,request⟩:=word_environment source.code.lookup (ofString "encode_execution_requests") (ofString "rq") body resultShape rq (original_code source.code data.arena.code)
  obtain ⟨heap,heapCell,lower,bounded,aligned⟩:=data.heap
  exact ⟨rq,heap,start,size,counts,callee,args,called,
    data.arena.code,data.arena.domain,data.little,image.of_memory (by intros; exact ⟨rfl,rfl⟩),request,heapCell,by omega,bounded,aligned⟩

/-- All original request bytes precede this invocation's incoming heap. -/
theorem Entry.input_before_heap {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts) :
    pointer.toNat+input.length%2^64+8≤heap.toNat := by
  have before:=entry.image.cursorAfterInput
  have afterRecord:=entry.heapLower
  omega

/-- Even a zero-length list has its real validated pointer; nonempty
copy operands and all their bytes are below the encoder's original heap. -/
theorem Entry.list_before_heap {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts) (index : Nat) (inside : index<5) :
    (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start index).toNat+
      (counts index).toNat*(Requests.elementSize index).toNat≤heap.toNat := by
  have extent:=entry.image.list_inside index inside
  have number:=byteAddress_toNat pointer (start+(Requests.offsetWord input start index).toNat)
    (by have upper:=entry.image.inputArena.upper; omega)
  have pointerNumber : (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start index).toNat=
      pointer.toNat+(start+(Requests.offsetWord input start index).toNat):=by
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using number
  rw [pointerNumber]
  have before:=entry.input_before_heap
  omega

end InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.list_bytes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.list_size_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.main_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.Entry.input_before_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.Entry.list_before_heap

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.caller_shape

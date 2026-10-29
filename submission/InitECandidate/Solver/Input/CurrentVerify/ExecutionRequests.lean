import InitECandidate.Solver.Input.CurrentVerify.Withdrawals
import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.CallPrefixLocalResult
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.ScalarStoreMemory
import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.Input.ClockCostCurrentValue
import InitECandidate.Solver.Input.CounterStrideLoop
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.WordPairLookup
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.MemoryConstantLoop
import InitECandidate.Solver.Input.CounterLoopLocal
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.StoppingPrefix
import InitECandidate.Solver.WitnessRadix.CopyNormalCall

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

def afterArrayAllocation : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def requestsLoopAndReturn : ProgHOL 64:=match afterArrayAllocation with | .dec _ _ _ (.dec _ _ _ rest)=>rest | _=>.skip
def iterationBody : ProgHOL 64:=match requestsLoopAndReturn with | .seq (.while _ rest) _=>rest | _=>.skip
def afterFields : ProgHOL 64:=match iterationBody with | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ rest))=>rest | _=>.skip

def sizeChoice (index width : Nat) : ProgHOL 64:=
  .ite (.cmp .equal (localVar "i") (.const (BitVec.ofNat 64 index)))
    (.assign .local (ofString "sz") (.const (BitVec.ofNat 64 width))) .skip

def sizeActions : List CallPrefix.Action:=[.command (sizeChoice 1 76),.command (sizeChoice 2 116),
  .command (sizeChoice 3 184),.command (sizeChoice 4 68)]
def sizeProgram : ProgHOL 64:=CallPrefix.program sizeActions .skip
def afterSizes : ProgHOL 64:=(CallPrefix.cutAt 4 afterFields).2

set_option maxRecDepth 100000 in
theorem size_prefix_shape : afterFields=CallPrefix.program sizeActions afterSizes := by
  simp only [afterFields,iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterSizes,CallPrefix.cutAt,CallPrefix.program,sizeActions,sizeChoice,localVar]

/-- The four width decisions are the actual straight-line local prefix. -/
theorem size_supported : StraightBody.accepts sizeProgram=true := by rfl

def sizeState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  if index=0 then source else bind source "sz" (Requests.elementSize index)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Execute the real four decisions from the actual i and initial sz=192.
This does not assume that the following allocation or copy will succeed. -/
theorem size_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (inside : index<5)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (initial : source.locals.lookup (ofString "sz")=some (.val (.word 192#64)))
    (tail : ProgHOL 64) :
    evaluateHOLFiniteState source (CallPrefix.program sizeActions tail)=evaluateHOLFiniteState (sizeState source index) tail := by
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;>
    simp [sizeProgram,CallPrefix.program,sizeActions,sizeChoice,sizeState,Requests.elementSize,
      evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_assign,evaluateHOLFiniteState_skip,
      evalHOLExact,evalListHOLExact,toExact,localVar,counter,initial,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,QueryBranch.bind,setVarHOLFinite,
      HolFiniteMapExact.update,FUPDATE,
      show ofString "i"≠ofString "sz" from by decide,show ofString "sz"≠ofString "i" from by decide]

theorem size_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (inside : index<5)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (initial : source.locals.lookup (ofString "sz")=some (.val (.word 192#64))) :
    evaluateHOLFiniteState source sizeProgram=(none,sizeState source index) := by
  simpa only [sizeProgram,evaluateHOLFiniteState_skip] using size_continue source index inside counter initial .skip

/-- Each chosen width is exactly the decoder's width for that request type. -/
theorem size_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (initial : source.locals.lookup (ofString "sz")=some (.val (.word 192#64))) :
    (sizeState source index).locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize index))) := by
  by_cases zero : index=0
  · subst index; simpa [sizeState,Requests.elementSize] using initial
  · simp only [sizeState,if_neg zero]; exact bind_lookup_same _ _ _

theorem size_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) :
    LocalEffects.erase (sizeState source index)=LocalEffects.erase source := by
  unfold sizeState
  split <;> rfl

def requestField (offset : Nat) : ExpHOL 64:=.load .one
  (.op .add [localVar "rq",.const (BitVec.ofNat 64 offset),.panop .mul [localVar "i",.const 16#64]])

def loopTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 5#64)
def loopReturn : ProgHOL 64:=.return (.rstruct [localVar "arr",localVar "n"])

set_option maxRecDepth 100000 in
theorem iteration_shape : iterationBody=.dec (ofString "p") .one (requestField 0)
    (.dec (ofString "cnt") .one (requestField 8)
      (.dec (ofString "sz") .one (.const 192#64) afterFields)) := by
  simp only [iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,afterFields,requestField,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem loop_shape : requestsLoopAndReturn=.seq (.while loopTest iterationBody) loopReturn := by
  simp only [requestsLoopAndReturn,afterArrayAllocation,body,iterationBody,loopTest,loopReturn,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

/-- The literal indexed load uses the accepted request record's owned word,
with the same actual local i. No encoded output cells are assumed. -/
theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rq word : BitVec 64) (index offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena rq 80) (aligned : rq.toNat%8=0)
    (inside : 16*index+offset<80) (multiple : offset%8=0)
    (request : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (cell : source.memory (rq+BitVec.ofNat 64 (16*index+offset))=.word word) :
    eval source (requestField offset)=some (.val (.word word)) := by
  have address : eval source (.op .add [localVar "rq",.const (BitVec.ofNat 64 offset),.panop .mul [localVar "i",.const 16#64]])=
      some (.val (.word (rq+BitVec.ofNat 64 (16*index+offset)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,request,counter,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_add,BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_comm,BitVec.add_assoc]
  exact Witness.load_word_read source _ _ word address
    (AllocatedBytes.word_mapped source rq 80 (16*index+offset) domain arena inside aligned (by omega)) cell

/-- Both actual list fields are already determined at a reached iteration. -/
theorem fields_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (image : Requests.DecodedImage input source pointer rq start size counts) (index : Nat) (inside : index<5)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (request : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source (requestField 0)=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start index))) ∧
    eval source (requestField 8)=some (.val (.word (counts index))) := by
  have cells:=image.image.cells index inside
  exact ⟨field_read source rq _ index 0 domain image.cursorArena image.cursorAligned (by omega) (by decide) request counter
    (by simpa only [Nat.add_zero] using cells.1),
    field_read source rq _ index 8 domain image.cursorArena image.cursorAligned (by omega) (by decide) request counter cells.2⟩

def nonemptyChoice : ProgHOL 64:=match afterSizes with | .seq first _=>first | _=>.skip
def incrementIndex : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])

set_option maxRecDepth 100000 in
theorem after_sizes_shape : afterSizes=.seq nonemptyChoice incrementIndex := by
  simp only [afterSizes,afterFields,iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    CallPrefix.cutAt,nonemptyChoice,incrementIndex,localVar]

set_option maxRecDepth 100000 in
/-- Whatever the real allocation/copy outcome, a continuing iteration
advances its own counter once. A stopped iteration needs no next state. -/
theorem iteration_advance : CounterFlow.Advances (ofString "i") 1 iterationBody := by
  simp only [iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | exact CounterFlow.increment _
    | apply CounterFlow.declared
    | apply CounterFlow.sequence (left:=0) (right:=1)
    | apply CounterFlow.preserved
    | apply LocalPrefix.dec
    | apply LocalPrefix.decCall
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | exact LocalPrefix.store _ _
    | exact LocalPrefix.storeByte _ _
    | exact LocalPrefix.skip
    | apply LocalPrefix.assign
    | exact LocalPrefix.call none _ _ (by simp)
    | decide

/-- Only rows already emitted by the current execution have an image. -/
structure EncodedSlice (array heap pointer length : BitVec 64) : Prop where
  positive : 1≤length.toNat
  bounded : length.toNat≤251655057
  arena : AllocatedBytes.Arena pointer length.toNat
  afterArray : array.toNat+80≤pointer.toNat
  beforeHeap : pointer.toNat+length.toNat≤heap.toNat

structure LoopModel (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer rq array : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) where
  index : Nat
  emitted : Nat
  heap : BitVec 64
  slices : Nat→BitVec 64×BitVec 64
  indexBound : index≤5
  emittedBound : emitted≤index
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  emittedCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 emitted)))
  requestCell : source.locals.lookup (ofString "rq")=some (.val (.word rq))
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  image : Requests.DecodedImage input source pointer rq start size counts
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  arrayArena : AllocatedBytes.Arena array 80
  arrayAligned : array.toNat%8=0
  requestBefore : rq.toNat+80≤array.toNat
  arrayBefore : array.toNat+80≤heap.toNat
  rows : ∀ row<emitted,source.memory (array+BitVec.ofNat 64 (16*row))=.word (slices row).1 ∧
    source.memory (array+BitVec.ofNat 64 (16*row+8))=.word (slices row).2 ∧
    EncodedSlice array heap (slices row).1 (slices row).2

/-- The original signed guard has the expected meaning at every actual
loop cursor, including the final i=5 state. -/
theorem LoopModel.test_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) :
    eval source loopTest=some (.val (.word (if model.index<5 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 model.index).toNat=model.index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bounded:=model.indexBound; omega)]
  have small : ¬9223372036854775808≤model.index:=by have bounded:=model.indexBound; omega
  simp [loopTest,eval,evalHOLExact,toExact,localVar,model.indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,small]

/-- Fresh allocations and descriptor writes need only preserve the two
real record fields per type to retain the whole decoded request image. -/
def LoopModel.of_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts)
    (frame : LocalEffects.erase target=LocalEffects.erase source)
    (indexCell : target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))))
    (emittedCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 model.emitted))))
    (requestCell : target.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (arrayCell : target.locals.lookup (ofString "arr")=some (.val (.word array))) :
    LoopModel input target pointer rq array start size counts := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have code:=congrArg PanSemStateFiniteExact.code frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change target.globals=source.globals at globals
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  refine {model with
    indexCell:=indexCell,emittedCell:=emittedCell,requestCell:=requestCell,arrayCell:=arrayCell,
    installed:=(by rw [code]; exact model.installed),domain:=domain.trans model.domain,little:=endian.trans model.little,
    image:=model.image.of_memory (by intro index inside; exact ⟨congrFun memory _,congrFun memory _⟩),
    heapCell:=(by rw [globals]; exact model.heapCell),rows:=?_}
  intro row inside
  obtain ⟨pointerCell,lengthCell,bounds⟩:=model.rows row inside
  exact ⟨(congrFun memory _).trans pointerCell,(congrFun memory _).trans lengthCell,bounds⟩

def setupArguments : List (ExpHOL 64):=[.panop .mul [.const 5#64,.const 16#64]]
def setupActions : List CallPrefix.Action:=[.scoped (ofString "arr") .one (ofString "alloc") setupArguments,
  .declare (ofString "n") .one (.const 0#64),.declare (ofString "i") .one (.const 0#64)]
def setupState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :=
  bind (bind (bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 80#64) "arr" heap) "n" 0#64) "i" 0#64

set_option maxRecDepth 100000 in
theorem setup_shape : body=CallPrefix.program setupActions requestsLoopAndReturn := by
  simp only [body,setupActions,setupArguments,requestsLoopAndReturn,afterArrayAllocation,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,CallPrefix.program]

theorem setup_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) setupArguments=some (PersistentAlloc.values 80#64) := by
  simp [setupArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord]

/-- The initial array call and two declarations cost at most two source
ticks, including the allocator's actual capacity failure. -/
theorem setup_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program setupActions .skip) 2 := by
  unfold setupActions CallPrefix.program
  apply PersistentAlloc.scoped_price code installed (tailPrice:=0)
  exact ClockCost.declared code _ _ _ _ _ (ClockCost.declared code _ _ _ _ _ (ClockCost.skip code))

/-- A real reached setup supplies the allocation's own room and exact
post-state; no ownership or initialized rows are supplied for its future. -/
theorem setup_reached {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts)
    (actual : CallPrefix.Execution source setupActions current) :
    heap.toNat+80≤2952790016 ∧ current=setupState source heap := by
  change CallPrefix.Execution source (.scoped (ofString "arr") .one (ofString "alloc") setupArguments::
    [.declare (ofString "n") .one (.const 0#64),.declare (ofString "i") .one (.const 0#64)]) current at actual
  obtain ⟨allocated,reached,rest⟩:=actual.head
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup 80#64 (PersistentAlloc.original_code source.code entry.installed)
  obtain ⟨child,returned,bodyRun,endpoint⟩:=reached.scoped_known (ofString "arr") .one (ofString "alloc") setupArguments
    (PersistentAlloc.values 80#64) PersistentAlloc.body callee .one (setup_args source) called
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child heap 80#64 amountCell entry.heapCell entry.heapBound
    (Trap.original_code source.code entry.installed) returned bodyRun
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {child with locals:=source.locals}=PersistentAlloc.post {source with clock:=source.clock-1} heap 80#64 at callerFrame
  have allocatedEq : allocated=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 80#64) "arr" heap:=by
    rw [endpoint,answer,callerFrame]
    rfl
  rw [allocatedEq] at rest
  have afterN:=rest.declare_next (.val (.word 0#64)) (by simp [eval,evalHOLExact])
  have afterI:=afterN.declare_next (.val (.word 0#64)) (by simp [eval,evalHOLExact])
  have currentEq : current=setupState source heap:=by cases afterI; rfl
  exact ⟨by change heap.toNat+(80#64).toNat≤2952790016 at room; simpa using room,currentEq⟩

/-- The real setup constructs the vacuous initial loop image. Array room
comes from its observed allocator; no later blob allocation is assumed. -/
theorem setup_model {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts)
    (actual : CallPrefix.Execution source setupActions current) :
    ∃ model : LoopModel input current pointer rq heap start size counts,model.index=0 ∧ model.emitted=0 ∧
      model.heap=PersistentAlloc.rounded heap 80#64 ∧ current.memory=source.memory := by
  obtain ⟨room,currentEq⟩:=setup_reached entry actual
  rw [currentEq]
  have guards:=PersistentAlloc.guards heap 80#64 room
  have lower : 2701131776≤heap.toNat:=by
    have a:=entry.image.inputLower
    have b:=entry.image.cursorAfterInput
    have c:=entry.heapLower
    omega
  have grows : heap.toNat+80≤(PersistentAlloc.rounded heap 80#64).toNat:=guards.2.2.1
  have nextCell : (setupState source heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 80#64))):=by
    simp [setupState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  refine ⟨{
    index:=0,emitted:=0,heap:=PersistentAlloc.rounded heap 80#64,slices:=fun _=>(0#64,0#64),
    indexBound:=by decide,emittedBound:=by decide,
    indexCell:=(by simp [setupState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]),
    emittedCell:=(by simp [setupState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]),
    requestCell:=(by simpa [setupState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.request),
    arrayCell:=(by simp [setupState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]),
    installed:=entry.installed,domain:=entry.domain,little:=entry.little,
    image:=entry.image.of_memory (by intro index inside; exact ⟨rfl,rfl⟩),heapCell:=nextCell,
    heapBound:=guards.2.2.2.1,heapAligned:=guards.2.2.2.2,
    arrayArena:=⟨lower,by omega⟩,arrayAligned:=entry.heapAligned,requestBefore:=entry.heapLower,arrayBefore:=grows,
    rows:=(by intro row inside; omega) },rfl,rfl,rfl,rfl⟩

def LoopModel.clocked {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (clock : Nat) :
    LoopModel input {source with clock:=clock} pointer rq array start size counts :=
  model.of_frame rfl model.indexCell model.emittedCell model.requestCell model.arrayCell

def fieldActions : List CallPrefix.Action:=[.declare (ofString "p") .one (requestField 0),
  .declare (ofString "cnt") .one (requestField 8),.declare (ofString "sz") .one (.const 192#64)]
def fieldsState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer count : BitVec 64) :=
  bind (bind (bind source "p" pointer) "cnt" count) "sz" 192#64

theorem fields_shape : iterationBody=CallPrefix.program fieldActions afterFields := iteration_shape

/-- The actual two record loads and initial width declaration reach their
specific current state, without assuming the following branch continues. -/
theorem LoopModel.fields_execution {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5) :
    CallPrefix.Execution source fieldActions
      (fieldsState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) (counts model.index)) := by
  let p:=pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index
  let sp:=bind source "p" p
  have reads:=fields_read model.image model.index active model.domain model.requestCell model.indexCell
  have countRead : eval sp (requestField 8)=some (.val (.word (counts model.index))):=
    field_read sp rq _ model.index 8 model.domain model.image.cursorArena model.image.cursorAligned (by omega) (by decide)
      ((bind_lookup_other source "p" "rq" p (by decide)).trans model.requestCell)
      ((bind_lookup_other source "p" "i" p (by decide)).trans model.indexCell) (model.image.image.cells model.index active).2
  exact .step (.declare source (ofString "p") .one (requestField 0) (.val (.word p)) reads.1 (by simp [shapeOfHOLExact,shapeEqHOL]))
    (.step (.declare sp (ofString "cnt") .one (requestField 8) (.val (.word (counts model.index))) countRead (by simp [shapeOfHOLExact,shapeEqHOL]))
      (.step (.declare (bind sp "cnt" (counts model.index)) (ofString "sz") .one (.const 192#64) (.val (.word 192#64))
        (by simp [eval,evalHOLExact]) (by simp [shapeOfHOLExact,shapeEqHOL])) (.done _)))

def preparedState (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (start index : Nat) (counts : Nat→BitVec 64) :=
  sizeState (fieldsState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start index) (counts index)) index

/-- Real field reads and width decisions retain the complete nonlocal
observation of the original iteration and its unchanged remaining branch. -/
theorem LoopModel.iteration_observe {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5) :
    CallPrefix.observe (evaluateHOLFiniteState source iterationBody)=
      CallPrefix.observe (evaluateHOLFiniteState (preparedState input source pointer start model.index counts) afterSizes) := by
  let entered:=fieldsState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) (counts model.index)
  have counter : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))):=by
    simpa [entered,fieldsState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.indexCell
  have initial : entered.locals.lookup (ofString "sz")=some (.val (.word 192#64)):=bind_lookup_same _ _ _
  calc
    _ = CallPrefix.observe (evaluateHOLFiniteState entered afterFields) := by
      simpa only [fields_shape] using (model.fields_execution active).observe afterFields
    _ = _ := by
      rw [size_prefix_shape,size_continue entered model.index active counter initial afterSizes]
      rfl

theorem prepared_frame (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (start index : Nat) (counts : Nat→BitVec 64) :
    LocalEffects.erase (preparedState input source pointer start index counts)=LocalEffects.erase source :=
  (size_frame _ index).trans rfl

theorem prepared_clock (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (start index : Nat) (counts : Nat→BitVec 64) :
    (preparedState input source pointer start index counts).clock=source.clock := by
  unfold preparedState sizeState
  split <;> rfl

theorem prepared_keeps (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (start index : Nat) (counts : Nat→BitVec 64) (key : MlS)
    (notPointer : key≠ofString "p") (notCount : key≠ofString "cnt") (notSize : key≠ofString "sz") :
    (preparedState input source pointer start index counts).locals.lookup key=source.locals.lookup key := by
  unfold preparedState sizeState
  split <;> simp [fieldsState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    notPointer,notCount,notSize,Ne.symm notPointer,Ne.symm notCount,Ne.symm notSize]

def LoopModel.prepared {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) :
    LoopModel input (preparedState input source pointer start model.index counts) pointer rq array start size counts :=
  model.of_frame (prepared_frame input source pointer start model.index counts)
    ((prepared_keeps input source pointer start model.index counts _ (by decide) (by decide) (by decide)).trans model.indexCell)
    ((prepared_keeps input source pointer start model.index counts _ (by decide) (by decide) (by decide)).trans model.emittedCell)
    ((prepared_keeps input source pointer start model.index counts _ (by decide) (by decide) (by decide)).trans model.requestCell)
    ((prepared_keeps input source pointer start model.index counts _ (by decide) (by decide) (by decide)).trans model.arrayCell)

theorem prepared_cells (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (start index : Nat) (counts : Nat→BitVec 64) :
    (preparedState input source pointer start index counts).locals.lookup (ofString "p")=
      some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start index))) ∧
    (preparedState input source pointer start index counts).locals.lookup (ofString "cnt")=some (.val (.word (counts index))) ∧
    (preparedState input source pointer start index counts).locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize index))) := by
  constructor
  · unfold preparedState sizeState
    split <;> simp [fieldsState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  constructor
  · unfold preparedState sizeState
    split <;> simp [fieldsState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · exact size_selected _ index (bind_lookup_same _ _ _)

def blobArguments : List (ExpHOL 64):=[.op .add [.panop .mul [localVar "cnt",localVar "sz"],.const 8#64]]
def afterBlob : ProgHOL 64:=match nonemptyChoice with | .ite _ (.decCall _ _ _ _ rest) _=>rest | _=>.skip
def blobBody : ProgHOL 64:=.decCall (ofString "blob") .one (ofString "alloc") blobArguments afterBlob
def tagStore : ProgHOL 64:=.storeByte (localVar "blob") (localVar "i")
def blobCopyArguments : List (ExpHOL 64):=[Scalar.plus (localVar "blob") 1,localVar "p",.panop .mul [localVar "cnt",localVar "sz"]]
def blobCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") blobCopyArguments
def descriptorFooter : ProgHOL 64:=match afterBlob with | .seq _ (.seq _ rest)=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem blob_shape : nonemptyChoice=.ite (.cmp .notEqual (localVar "cnt") (.const 0#64)) blobBody .skip ∧
    afterBlob=.seq tagStore (.seq blobCopy descriptorFooter) := by
  simp only [nonemptyChoice,afterSizes,afterFields,iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    CallPrefix.cutAt,blobBody,blobArguments,afterBlob,tagStore,blobCopy,blobCopyArguments,descriptorFooter,Scalar.plus,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem descriptor_supported : StraightBody.accepts descriptorFooter=true := by
  simp only [descriptorFooter,afterBlob,nonemptyChoice,afterSizes,afterFields,iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cutAt]
  rfl

theorem descriptor_cost (code) : ClockCost.Bound code descriptorFooter 0 :=
  ClockCost.of_quiet code descriptorFooter (StraightBody.effects (ofString "rq") code descriptorFooter descriptor_supported).1

/-- The real memcpy operands at the blob branch, before or after its tag
store. Its length is the original product word, with no alternative encoder. -/
theorem blob_copy_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer blob count width : BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (b : source.locals.lookup (ofString "blob")=some (.val (.word blob)))
    (c : source.locals.lookup (ofString "cnt")=some (.val (.word count)))
    (w : source.locals.lookup (ofString "sz")=some (.val (.word width))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) blobCopyArguments=
      some (CopyGeneral.values (blob+1#64) pointer (count*width).toNat) := by
  simp only [CopyGeneral.values,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  simp [blobCopyArguments,Scalar.plus,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
    p,b,c,w,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

def tagState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (blob : BitVec 64) (index : Nat) :=
  {source with memory:=ByteStore.put source.memory source.be blob (BitVec.ofNat 8 index)}

theorem tag_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (blob : BitVec 64) (index span : Nat)
    (active : index<5) (positive : 0<span) (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena blob span)
    (b : source.locals.lookup (ofString "blob")=some (.val (.word blob)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evaluateHOLFiniteState source tagStore=(none,tagState source blob index) := by
  have byteNumber : (BitVec.ofNat 8 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  apply ByteStore.execute source (localVar "blob") (localVar "i") blob (BitVec.ofNat 8 index)
  · simpa [eval,evalHOLExact,toExact,localVar] using b
  · rw [byteNumber]
    simpa [eval,evalHOLExact,toExact,localVar] using i
  · simpa [byteAddress] using AllocatedBytes.byte_mapped source blob span 0 domain arena positive

/-- After its actual allocation, the original tag/copy/descriptor suffix
has a linear all-outcome copy allowance. The owned destination is exactly
the newly checked blob; the source is the same decoded input list. -/
theorem after_blob_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer blob count width : BitVec 64)
    (index : Nat) (active : index<5) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (b : source.locals.lookup (ofString "blob")=some (.val (.word blob)))
    (c : source.locals.lookup (ofString "cnt")=some (.val (.word count)))
    (w : source.locals.lookup (ofString "sz")=some (.val (.word width)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (src : AllocatedBytes.Arena pointer (count*width).toNat)
    (dst : AllocatedBytes.Arena blob ((count*width).toNat+8)) :
    source.clock-(evaluateHOLFiniteState source afterBlob).2.clock≤(count*width).toNat/8+8 := by
  let tagged:=tagState source blob index
  have tagRun:=tag_execute source blob index ((count*width).toNat+8) active (by omega) domain dst b i
  have output : AllocatedBytes.Arena (blob+1#64) (count*width).toNat:=by
    simpa only [byteAddress] using dst.subrange blob ((count*width).toNat+8) 1 (count*width).toNat (by omega)
  have copyPrice:=CopyGeneral.call_cost_blocks tagged blobCopyArguments pointer (blob+1#64) (count*width).toNat
    (blob_copy_args tagged pointer blob count width p b c w) (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped tagged pointer (blob+1#64) (count*width).toNat domain src output)
    (by have upper:=src.upper; omega)
  have suffixPrice:=ClockCost.sequence_current tagged blobCopy descriptorFooter ((count*width).toNat/8+8) 0 copyPrice (descriptor_cost source.code)
  have observed:=CallPrefix.Reaches.project (CallPrefix.Reaches.command source tagged tagStore tagRun) (.seq blobCopy descriptorFooter)
  have clocks:=congrArg Prod.snd observed
  change (evaluateHOLFiniteState source (.seq tagStore (.seq blobCopy descriptorFooter))).2.clock=
    (evaluateHOLFiniteState tagged (.seq blobCopy descriptorFooter)).2.clock at clocks
  rw [blob_shape.2,clocks]
  exact suffixPrice

theorem blob_allocation_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count width : BitVec 64)
    (c : source.locals.lookup (ofString "cnt")=some (.val (.word count)))
    (w : source.locals.lookup (ofString "sz")=some (.val (.word width))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) blobArguments=
      some (PersistentAlloc.values (count*width+8#64)) := by
  simp [blobArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,c,w,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

/-- The original guarded blob allocation and its real tag/copy/descriptor
suffix are bounded even when the allocation fails. Natural room and the
mapped destination are derived only from the same normal allocator return. -/
theorem LoopModel.blob_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index))))
    (cntCell : source.locals.lookup (ofString "cnt")=some (.val (.word (counts model.index))))
    (szCell : source.locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize model.index)))) :
    source.clock-(evaluateHOLFiniteState source blobBody).2.clock≤(counts model.index*Requests.elementSize model.index).toNat/8+10 := by
  let bytes:=(counts model.index*Requests.elementSize model.index).toNat
  let amount:=counts model.index*Requests.elementSize model.index+8#64
  have bytesBound : bytes≤251655056:=by
    dsimp only [bytes]
    rw [list_size_number model.image model.index active]
    have budget:=list_bytes model.image model.index active
    omega
  have amountNumber : amount.toNat=bytes+8:=by
    dsimp only [amount]
    rw [BitVec.toNat_add_of_lt (by change bytes+8<2^64; omega)]
    rfl
  have args:=blob_allocation_args source (counts model.index) (Requests.elementSize model.index) cntCell szCell
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code model.installed)
  have inputArena : AllocatedBytes.Arena (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) bytes:=by
    dsimp only [bytes]
    rw [list_size_number model.image model.index active]
    exact model.image.list_arena model.index active
  have priced:=ClockCost.scoped_reached_current source "blob" .one (ofString "alloc") blobArguments (PersistentAlloc.values amount)
    PersistentAlloc.body afterBlob callee .one 1 (bytes/8+8) args called
    (PersistentAlloc.body_price source.code model.installed (callEntryStateHOLFinite source callee) rfl) (by
      intro child returned bodyRun checked
      obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child model.heap amount amountCell model.heapCell model.heapBound
        (Trap.original_code source.code model.installed) returned bodyRun
      have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
      change {child with locals:=source.locals}=PersistentAlloc.post {source with clock:=source.clock-1} model.heap amount at callerFrame
      let fresh:=bind (PersistentAlloc.post {source with clock:=source.clock-1} model.heap amount) "blob" model.heap
      have readyEq : CallNormal.continuationEntry source child "blob" returned=fresh:=by
        unfold CallNormal.continuationEntry
        rw [answer,callerFrame]
        rfl
      have mapped : AllocatedBytes.Arena model.heap (bytes+8):=by
        constructor
        · have first:=model.arrayArena.lower; have before:=model.arrayBefore; omega
        · rw [amountNumber] at room; omega
      have pFresh : fresh.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index))):=by
        simpa [fresh,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using pCell
      have cntFresh : fresh.locals.lookup (ofString "cnt")=some (.val (.word (counts model.index))):=by
        simpa [fresh,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using cntCell
      have szFresh : fresh.locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize model.index))):=by
        simpa [fresh,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using szCell
      have iFresh : fresh.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))):=by
        simpa [fresh,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.indexCell
      have suffixPrice:=after_blob_cost fresh _ model.heap (counts model.index) (Requests.elementSize model.index) model.index active model.installed model.domain
        pFresh (bind_lookup_same _ _ _) cntFresh szFresh iFresh inputArena mapped
      have clockEq : fresh.clock=child.clock:=by rw [←readyEq]; rfl
      rw [readyEq,←clockEq]
      exact suffixPrice)
  change source.clock-(evaluateHOLFiniteState source blobBody).2.clock≤1+(bytes/8+8)+1 at priced
  change source.clock-(evaluateHOLFiniteState source blobBody).2.clock≤bytes/8+10
  omega

/-- Every outcome of the complete original iteration is priced at its
actual current list size. The branch allocation derives its own room. -/
theorem LoopModel.iteration_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5) :
    source.clock-(evaluateHOLFiniteState source iterationBody).2.clock≤(counts model.index*Requests.elementSize model.index).toNat/8+10 := by
  let prepared:=preparedState input source pointer start model.index counts
  let bytes:=(counts model.index*Requests.elementSize model.index).toNat
  have cells:=prepared_cells input source pointer start model.index counts
  have blobPrice:=model.prepared.blob_cost active cells.1 cells.2.1 cells.2.2
  have branchPrice : prepared.clock-(evaluateHOLFiniteState prepared nonemptyChoice).2.clock≤bytes/8+10:=by
    rw [blob_shape.1]
    simpa only [Nat.max_zero] using ClockCost.conditional_current prepared _ blobBody .skip (bytes/8+10) 0 blobPrice
      (ClockCost.skip prepared.code prepared rfl)
  have priced:=ClockCost.sequence_current prepared nonemptyChoice incrementIndex (bytes/8+10) 0 branchPrice
    (ClockCost.assign prepared.code (ofString "i") (.op .add [localVar "i",.const 1#64]))
  have clocks:=congrArg (fun observation=>observation.1.2) (model.iteration_observe active)
  change (evaluateHOLFiniteState source iterationBody).2.clock=(evaluateHOLFiniteState prepared afterSizes).2.clock at clocks
  rw [←after_sizes_shape] at priced
  change prepared.clock-(evaluateHOLFiniteState prepared afterSizes).2.clock≤bytes/8+10 at priced
  rw [prepared_clock input source pointer start model.index counts] at priced
  rw [clocks]
  exact priced

/-- A convenient fixed iteration allowance, derived from the actual shared
request byte budget rather than the word width or arbitrary array contents. -/
theorem LoopModel.iteration_uniform {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5) :
    source.clock-(evaluateHOLFiniteState source iterationBody).2.clock≤31456889 := by
  have price:=model.iteration_cost active
  have number:=list_size_number model.image model.index active
  have budget:=list_bytes model.image model.index active
  omega

/-- Original lexical restoration affects only p/cnt/sz. Every other
actual post-iteration local agrees with that same prepared continuation. -/
theorem LoopModel.iteration_local {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (key : MlS) (notPointer : key≠ofString "p") (notCount : key≠ofString "cnt") (notSize : key≠ofString "sz") :
    (evaluateHOLFiniteState source iterationBody).2.locals.lookup key=
      (evaluateHOLFiniteState (preparedState input source pointer start model.index counts) afterSizes).2.locals.lookup key := by
  let entered:=fieldsState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) (counts model.index)
  have counter : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))):=by
    simpa [entered,fieldsState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.indexCell
  have initial : entered.locals.lookup (ofString "sz")=some (.val (.word 192#64)):=bind_lookup_same _ _ _
  have avoids : ∀ action∈fieldActions,action.avoids key:=by
    intro action member
    simp only [fieldActions,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact Ne.symm notPointer
    · exact Ne.symm notCount
    · exact Ne.symm notSize
  calc
    _ = (evaluateHOLFiniteState entered afterFields).2.locals.lookup key := by
      simpa only [fields_shape] using (model.fields_execution active).local_result key avoids afterFields
    _ = _ := by
      rw [size_prefix_shape,size_continue entered model.index active counter initial afterSizes]
      rfl

def descriptorPointer : ExpHOL 64:=.op .add [localVar "arr",.panop .mul [localVar "n",.const 16#64]]
def descriptorLength : ExpHOL 64:=.op .add [localVar "arr",.panop .mul [localVar "n",.const 16#64],.const 8#64]
def encodedLength : ExpHOL 64:=.op .add [.panop .mul [localVar "cnt",localVar "sz"],.const 1#64]
def incrementEmitted : ProgHOL 64:=.assign .local (ofString "n") (.op .add [localVar "n",.const 1#64])
def descriptorState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array blob count width : BitVec 64) (emitted : Nat) :=
  bind {source with memory:=(StoreWord.put (StoreWord.put source.memory (array+BitVec.ofNat 64 (16*emitted)) blob)
    (array+BitVec.ofNat 64 (16*emitted+8)) (count*width+1#64))} "n" (BitVec.ofNat 64 emitted+1#64)

set_option maxRecDepth 100000 in
theorem descriptor_shape : descriptorFooter=.seq (.store descriptorPointer (localVar "blob"))
    (.seq (.store descriptorLength encodedLength) incrementEmitted) := by
  simp only [descriptorFooter,afterBlob,nonemptyChoice,afterSizes,afterFields,iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cutAt,
    descriptorPointer,descriptorLength,encodedLength,incrementEmitted,localVar]

/-- Both real descriptor stores and n++ execute at the current empty slot.
No descriptor cell is assumed initialized before its own write. -/
theorem descriptor_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array blob count width : BitVec 64)
    (emitted : Nat) (inside : emitted<5) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena array 80) (aligned : array.toNat%8=0)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 emitted))))
    (b : source.locals.lookup (ofString "blob")=some (.val (.word blob)))
    (c : source.locals.lookup (ofString "cnt")=some (.val (.word count)))
    (w : source.locals.lookup (ofString "sz")=some (.val (.word width))) :
    evaluateHOLFiniteState source descriptorFooter=(none,descriptorState source array blob count width emitted) := by
  have pointerRead : eval source descriptorPointer=some (.val (.word (array+BitVec.ofNat 64 (16*emitted)))):=by
    simp [eval,descriptorPointer,evalHOLExact,evalListHOLExact,toExact,localVar,a,n,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,Nat.mul_comm,BitVec.mul_comm]
  have lengthRead : eval source descriptorLength=some (.val (.word (array+BitVec.ofNat 64 (16*emitted+8)))):=by
    simp [eval,descriptorLength,evalHOLExact,evalListHOLExact,toExact,localVar,a,n,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm,BitVec.mul_comm,BitVec.add_assoc]
  have blobRead : eval source (localVar "blob")=some (.val (.word blob)):=by simp [eval,evalHOLExact,toExact,localVar,b]
  have sizeRead : eval source encodedLength=some (.val (.word (count*width+1#64))):=by
    simp [eval,encodedLength,evalHOLExact,evalListHOLExact,toExact,localVar,c,w,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have pointerMapped:=AllocatedBytes.word_mapped source array 80 (16*emitted) domain arena (by omega) aligned (by omega)
  have lengthMapped:=AllocatedBytes.word_mapped source array 80 (16*emitted+8) domain arena (by omega) aligned (by omega)
  let sp:={source with memory:=StoreWord.put source.memory (array+BitVec.ofNat 64 (16*emitted)) blob}
  let sl:={sp with memory:=StoreWord.put sp.memory (array+BitVec.ofNat 64 (16*emitted+8)) (count*width+1#64)}
  have first : evaluateHOLFiniteState source (.store descriptorPointer (localVar "blob"))=(none,sp):=
    StoreWord.execute source descriptorPointer (localVar "blob") _ blob pointerRead blobRead pointerMapped
  have second : evaluateHOLFiniteState sp (.store descriptorLength encodedLength)=(none,sl):=
    StoreWord.execute sp descriptorLength encodedLength _ (count*width+1#64) lengthRead sizeRead lengthMapped
  have advancedRead : eval sl (.op .add [localVar "n",.const 1#64])=some (.val (.word (BitVec.ofNat 64 emitted+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,show sl.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 emitted))) from n,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have advanced:=StateSteps.assign_execute sl "n" (.op .add [localVar "n",.const 1#64]) (BitVec.ofNat 64 emitted) (BitVec.ofNat 64 emitted+1#64) n advancedRead
  rw [descriptor_shape,evaluateHOLFiniteState_seq_line780,first]
  change evaluateHOLFiniteState sp (.seq (.store descriptorLength encodedLength) incrementEmitted)=_
  rw [evaluateHOLFiniteState_seq_line780,second]
  exact advanced

def afterBlobState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array blob count width : BitVec 64)
    (index emitted : Nat) :=
  descriptorState (CopyGeneral.callState (tagState source blob index) pointer (blob+1#64) (count*width).toNat) array blob count width emitted

/-- A real normal suffix derives memcpy's own clock funding and the exact
new descriptor state. Neither a later copy return nor its funding is an
entry hypothesis; only this invocation's normal result is inspected. -/
theorem after_blob_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array blob count width : BitVec 64)
    (index emitted : Nat) (active : index<5) (inside : emitted<5)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 emitted))))
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (b : source.locals.lookup (ofString "blob")=some (.val (.word blob)))
    (c : source.locals.lookup (ofString "cnt")=some (.val (.word count)))
    (w : source.locals.lookup (ofString "sz")=some (.val (.word width)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (arrayArena : AllocatedBytes.Arena array 80) (arrayAligned : array.toNat%8=0)
    (src : AllocatedBytes.Arena pointer (count*width).toNat) (dst : AllocatedBytes.Arena blob ((count*width).toNat+8))
    (normal : evaluateHOLFiniteState source afterBlob=(none,target)) :
    CopyGeneral.cost pointer (blob+1#64) (count*width).toNat+1≤source.clock ∧
      target=afterBlobState source pointer array blob count width index emitted := by
  let tagged:=tagState source blob index
  have tagRun:=tag_execute source blob index ((count*width).toNat+8) active (by omega) domain dst b i
  rw [blob_shape.2,evaluateHOLFiniteState_seq_line780,tagRun] at normal
  change evaluateHOLFiniteState tagged (.seq blobCopy descriptorFooter)=(none,target) at normal
  obtain ⟨copied,copyRun,remaining⟩:=sequence_none tagged target blobCopy descriptorFooter normal
  have output : AllocatedBytes.Arena (blob+1#64) (count*width).toNat:=by
    simpa only [byteAddress] using dst.subrange blob ((count*width).toNat+8) 1 (count*width).toNat (by omega)
  obtain ⟨funded,price,copiedEq⟩:=CopyGeneral.call_normal tagged copied blobCopyArguments pointer (blob+1#64) (count*width).toNat
    (blob_copy_args tagged pointer blob count width p b c w) (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped tagged pointer (blob+1#64) (count*width).toNat domain src output)
    (by have upper:=src.upper; omega) copyRun
  rw [copiedEq] at remaining
  have footerRun:=descriptor_execute (CopyGeneral.callState tagged pointer (blob+1#64) (count*width).toNat) array blob count width emitted inside domain
    arrayArena arrayAligned a n b c w
  exact ⟨funded,congrArg Prod.snd (remaining.symm.trans footerRun)⟩

theorem descriptor_numbers (array : BitVec 64) (emitted : Nat) (inside : emitted<5) (arena : AllocatedBytes.Arena array 80) :
    (array+BitVec.ofNat 64 (16*emitted)).toNat=array.toNat+16*emitted ∧
    (array+BitVec.ofNat 64 (16*emitted+8)).toNat=array.toNat+16*emitted+8 := by
  have upper:=arena.upper
  exact ⟨byteAddress_toNat array (16*emitted) (by omega),by
    have number:=byteAddress_toNat array (16*emitted+8) (by omega)
    change (array+BitVec.ofNat 64 (16*emitted+8)).toNat=array.toNat+(16*emitted+8) at number
    omega⟩

theorem descriptor_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array blob count width : BitVec 64)
    (emitted : Nat) (inside : emitted<5) (arena : AllocatedBytes.Arena array 80) :
    (descriptorState source array blob count width emitted).memory (array+BitVec.ofNat 64 (16*emitted))=.word blob ∧
    (descriptorState source array blob count width emitted).memory (array+BitVec.ofNat 64 (16*emitted+8))=.word (count*width+1#64) := by
  have numbers:=descriptor_numbers array emitted inside arena
  have different : array+BitVec.ofNat 64 (16*emitted)≠array+BitVec.ofNat 64 (16*emitted+8):=by
    intro equal
    have number:=congrArg BitVec.toNat equal
    omega
  exact ⟨by change StoreWord.put (StoreWord.put source.memory _ blob) _ (count*width+1#64) _=_; simp [StoreWord.put,different],by exact if_pos rfl⟩

/-- Descriptor writes protect the entire preceding array prefix, including
all real earlier row words and the complete earlier decoded input. -/
theorem descriptor_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array blob count width query : BitVec 64)
    (emitted : Nat) (inside : emitted<5) (arena : AllocatedBytes.Arena array 80) (before : query.toNat<array.toNat+16*emitted) :
    (descriptorState source array blob count width emitted).memory query=source.memory query := by
  have numbers:=descriptor_numbers array emitted inside arena
  have notPointer : query≠array+BitVec.ofNat 64 (16*emitted):=by intro equal; have number:=congrArg BitVec.toNat equal; omega
  have notLength : query≠array+BitVec.ofNat 64 (16*emitted+8):=by intro equal; have number:=congrArg BitVec.toNat equal; omega
  change StoreWord.put (StoreWord.put source.memory _ blob) _ (count*width+1#64) query=_
  simp [StoreWord.put,notPointer,notLength]

/-- The unaligned payload at blob+1 stays inside the same owned blob;
its backing words cannot touch anything below that aligned allocation. -/
theorem copy_after_tag_away (blob query : BitVec 64) (length : Nat) (arena : AllocatedBytes.Arena blob (length+8))
    (aligned : blob.toNat%8=0) (before : query.toNat<blob.toNat) : CopyGeneral.Away (blob+1#64) query length := by
  have whole:=arena.away_below blob query (length+8) aligned before
  intro offset inside
  have address : byteAddress (blob+1#64) offset=byteAddress blob (offset+1):=by
    simp only [byteAddress,BitVec.ofNat_add]
    rw [BitVec.add_assoc,BitVec.add_comm (1#64) (BitVec.ofNat 64 offset)]
  simpa only [address] using whole (offset+1) (by omega)

theorem after_blob_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array blob count width : BitVec 64)
    (index emitted : Nat) : MemoryMetadata.erase (afterBlobState source pointer array blob count width index emitted)=MemoryMetadata.erase source := rfl

/-- The complete real normal suffix protects previous rows and all earlier
input cells. Both the tag and memcpy stay in the same fresh allocation. -/
theorem after_blob_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array blob count width query : BitVec 64)
    (index emitted : Nat) (inside : emitted<5) (arrayArena : AllocatedBytes.Arena array 80)
    (blobArena : AllocatedBytes.Arena blob ((count*width).toNat+8)) (blobAligned : blob.toNat%8=0)
    (afterArray : array.toNat+80≤blob.toNat) (before : query.toNat<array.toNat+16*emitted) :
    (afterBlobState source pointer array blob count width index emitted).memory query=source.memory query := by
  have below : query.toNat<blob.toNat:=by omega
  have whole:=blobArena.away_below blob query ((count*width).toNat+8) blobAligned below
  have notBacking : query≠panByteAlignHOL (width:=64) blob:=by
    simpa [byteAddress] using (whole 0 (by omega)).2
  calc
    _ = (CopyGeneral.callState (tagState source blob index) pointer (blob+1#64) (count*width).toNat).memory query :=
      descriptor_prefix _ array blob count width query emitted inside arrayArena before
    _ = (tagState source blob index).memory query :=
      CopyGeneral.call_memory_away _ pointer (blob+1#64) query (count*width).toNat (copy_after_tag_away blob query (count*width).toNat blobArena blobAligned below)
    _ = source.memory query := ByteStore.away source.memory source.be blob query (BitVec.ofNat 8 index) notBacking

def blobAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count width : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (count*width+8#64)) "blob" heap

/-- The same real normal blob branch derives its checked natural room and
complete post-state, including the original scoped blob restoration. -/
theorem LoopModel.blob_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index))))
    (cntCell : source.locals.lookup (ofString "cnt")=some (.val (.word (counts model.index))))
    (szCell : source.locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize model.index))))
    (normal : evaluateHOLFiniteState source blobBody=(none,target)) :
    model.heap.toNat+(counts model.index*Requests.elementSize model.index).toNat+8≤2952790016 ∧
      target=restore source "blob" (afterBlobState (blobAllocated source model.heap (counts model.index) (Requests.elementSize model.index))
        (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) array model.heap
        (counts model.index) (Requests.elementSize model.index) model.index model.emitted) := by
  let bytes:=(counts model.index*Requests.elementSize model.index).toNat
  let amount:=counts model.index*Requests.elementSize model.index+8#64
  have bytesBound : bytes≤251655056:=by
    dsimp only [bytes]
    rw [list_size_number model.image model.index active]
    have budget:=list_bytes model.image model.index active
    omega
  have amountNumber : amount.toNat=bytes+8:=by
    dsimp only [amount]
    rw [BitVec.toNat_add_of_lt (by change bytes+8<2^64; omega)]
    rfl
  have args:=blob_allocation_args source (counts model.index) (Requests.elementSize model.index) cntCell szCell
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code model.installed)
  obtain ⟨funded,child,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target "blob" .one (ofString "alloc") blobArguments
    (PersistentAlloc.values amount) PersistentAlloc.body afterBlob callee .one args called normal
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child model.heap amount amountCell model.heapCell model.heapBound
    (Trap.original_code source.code model.installed) returned bodyRun
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {child with locals:=source.locals}=PersistentAlloc.post {source with clock:=source.clock-1} model.heap amount at callerFrame
  let fresh:=blobAllocated source model.heap (counts model.index) (Requests.elementSize model.index)
  have readyEq : CallNormal.continuationEntry source child "blob" returned=fresh:=by
    unfold CallNormal.continuationEntry
    rw [answer,callerFrame]
    rfl
  rw [readyEq] at continued
  have inputArena : AllocatedBytes.Arena (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index) bytes:=by
    dsimp only [bytes]
    rw [list_size_number model.image model.index active]
    exact model.image.list_arena model.index active
  have mapped : AllocatedBytes.Arena model.heap (bytes+8):=by
    constructor
    · have first:=model.arrayArena.lower; have before:=model.arrayBefore; omega
    · rw [amountNumber] at room; omega
  have cells : fresh.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      fresh.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 model.emitted))) ∧
      fresh.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index))) ∧
      fresh.locals.lookup (ofString "cnt")=some (.val (.word (counts model.index))) ∧
      fresh.locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize model.index))) ∧
      fresh.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))):=by
    simpa [fresh,blobAllocated,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using
      And.intro model.arrayCell (And.intro model.emittedCell (And.intro pCell (And.intro cntCell (And.intro szCell model.indexCell))))
  obtain ⟨copyFunded,innerEq⟩:=after_blob_normal fresh inner _ array model.heap (counts model.index) (Requests.elementSize model.index) model.index model.emitted
    active (by have bounded:=model.emittedBound; omega) model.installed model.domain cells.1 cells.2.1 cells.2.2.1
    (bind_lookup_same _ _ _) cells.2.2.2.1 cells.2.2.2.2.1 cells.2.2.2.2.2 model.arrayArena model.arrayAligned inputArena mapped continued
  refine ⟨by rw [amountNumber] at room; omega,?_⟩
  rw [endpoint,innerEq]

theorem choice_preserves (key : MlS) (notBlob : key≠ofString "blob") (notCount : key≠ofString "n") :
    LocalPrefix key nonemptyChoice := by
  rw [blob_shape.1,blobBody,blob_shape.2,descriptor_shape]
  exact .ite _ (.decCall (ofString "blob") .one (ofString "alloc") blobArguments notBlob
    (.seq (.storeByte _ _) (.seq (.call none _ _ (by simp))
      (.seq (.store _ _) (.seq (.store _ _) (.assign (ofString "n") _ notCount)))))) .skip

theorem LoopModel.increment_execute {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) :
    evaluateHOLFiniteState source incrementIndex=(none,bind source "i" (BitVec.ofNat 64 model.index+1#64)) := by
  apply StateSteps.assign_execute source "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 model.index) _ model.indexCell
  simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- A skipped empty list advances i and retains exactly the old row image;
it does not preinitialize a row or request another allocation. -/
def LoopModel.skip_next {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5) :
    LoopModel input (bind source "i" (BitVec.ofNat 64 model.index+1#64)) pointer rq array start size counts :=
  {model with
    index:=model.index+1,indexBound:=(by omega),emittedBound:=(by have bounded:=model.emittedBound; omega),
    indexCell:=(by simpa only [BitVec.ofNat_add] using bind_lookup_same source "i" (BitVec.ofNat 64 model.index+1#64)),
    emittedCell:=(bind_lookup_other source "i" "n" _ (by decide)).trans model.emittedCell,
    requestCell:=(bind_lookup_other source "i" "rq" _ (by decide)).trans model.requestCell,
    arrayCell:=(bind_lookup_other source "i" "arr" _ (by decide)).trans model.arrayCell,
    image:=model.image.of_memory (by intro index inside; exact ⟨rfl,rfl⟩)}

def emittedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width : BitVec 64)
    (index emitted : Nat) :=
  bind (restore source "blob" (afterBlobState (blobAllocated source heap count width) pointer array heap count width index emitted))
    "i" (BitVec.ofNat 64 index+1#64)

theorem emitted_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width : BitVec 64)
    (index emitted : Nat) :
    MemoryMetadata.erase (emittedState source pointer array heap count width index emitted)=
      MemoryMetadata.erase (PersistentAlloc.post source heap (count*width+8#64)) := rfl

theorem emitted_keeps (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width : BitVec 64)
    (index emitted : Nat) (key : String) (notIndex : ofString key≠ofString "i") (notCount : ofString key≠ofString "n")
    (notBlob : ofString key≠ofString "blob") :
    (emittedState source pointer array heap count width index emitted).locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
  unfold emittedState
  rw [bind_lookup_other _ "i" key _ (Ne.symm notIndex),restore_lookup_other source _ "blob" key notBlob]
  unfold afterBlobState descriptorState
  rw [bind_lookup_other _ "n" key _ (Ne.symm notCount)]
  change (blobAllocated source heap count width).locals.lookup (ofString key)=source.locals.lookup (ofString key)
  exact bind_lookup_other _ "blob" key _ (Ne.symm notBlob)

theorem emitted_count_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width : BitVec 64)
    (index emitted : Nat) :
    (emittedState source pointer array heap count width index emitted).locals.lookup (ofString "n")=
      some (.val (.word (BitVec.ofNat 64 emitted+1#64))) := by
  unfold emittedState
  rw [bind_lookup_other _ "i" "n" _ (by decide),restore_lookup_other source _ "blob" "n" (by decide)]
  exact bind_lookup_same _ "n" _

theorem emitted_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width query : BitVec 64)
    (index emitted : Nat) (inside : emitted<5) (arrayArena : AllocatedBytes.Arena array 80)
    (blobArena : AllocatedBytes.Arena heap ((count*width).toNat+8)) (heapAligned : heap.toNat%8=0)
    (afterArray : array.toNat+80≤heap.toNat) (before : query.toNat<array.toNat+16*emitted) :
    (emittedState source pointer array heap count width index emitted).memory query=source.memory query :=
  after_blob_prefix (blobAllocated source heap count width) pointer array heap count width query index emitted inside arrayArena blobArena heapAligned afterArray before

theorem emitted_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array heap count width : BitVec 64)
    (index emitted : Nat) (inside : emitted<5) (arena : AllocatedBytes.Arena array 80) :
    (emittedState source pointer array heap count width index emitted).memory (array+BitVec.ofNat 64 (16*emitted))=.word heap ∧
    (emittedState source pointer array heap count width index emitted).memory (array+BitVec.ofNat 64 (16*emitted+8))=.word (count*width+1#64) :=
  descriptor_cells (CopyGeneral.callState (tagState (blobAllocated source heap count width) heap index)
    pointer (heap+1#64) (count*width).toNat) array heap count width emitted inside arena

/-- Construct just the next nonempty-list image from its own checked
allocation and exact executed writes. No later rows or calls are supplied. -/
def LoopModel.emit_next {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (room : model.heap.toNat+(counts model.index*Requests.elementSize model.index).toNat+8≤2952790016) :
    LoopModel input (emittedState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index)
      array model.heap (counts model.index) (Requests.elementSize model.index) model.index model.emitted) pointer rq array start size counts := by
  let count:=counts model.index
  let width:=Requests.elementSize model.index
  let p:=pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index
  let bytes:=(count*width).toNat
  let amount:=count*width+8#64
  let final:=emittedState source p array model.heap count width model.index model.emitted
  let nextHeap:=PersistentAlloc.rounded model.heap amount
  let slices:=Function.update model.slices model.emitted (model.heap,count*width+1#64)
  have bytesBound : bytes≤251655056:=by
    dsimp only [bytes,count,width]
    rw [list_size_number model.image model.index active]
    have budget:=list_bytes model.image model.index active
    omega
  have amountNumber : amount.toNat=bytes+8:=by
    dsimp only [amount]
    rw [BitVec.toNat_add_of_lt (by change bytes+8<2^64; omega)]
    rfl
  have lengthNumber : (count*width+1#64).toNat=bytes+1:=by
    rw [BitVec.toNat_add_of_lt (by change bytes+1<2^64; omega)]
    rfl
  have guards:=PersistentAlloc.guards model.heap amount (by rw [amountNumber]; exact room)
  have grows : model.heap.toNat+bytes+8≤nextHeap.toNat:=by
    have bounded:=guards.2.2.1
    rw [amountNumber] at bounded
    exact bounded
  have lower : 2701131776≤model.heap.toNat:=by have first:=model.arrayArena.lower; have before:=model.arrayBefore; omega
  have blobArena : AllocatedBytes.Arena model.heap (bytes+8):=⟨lower,by omega⟩
  have globals:=congrArg PanSemStateFiniteExact.globals (emitted_metadata source p array model.heap count width model.index model.emitted)
  change final.globals=source.globals.update (ofString "heap_ptr",.val (.word nextHeap)) at globals
  have heapCell : final.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)):=by rw [globals]; simp [HolFiniteMapExact.update,FUPDATE]
  have emittedInside : model.emitted<5:=by have bounded:=model.emittedBound; omega
  have earlier (query : BitVec 64) (before : query.toNat<array.toNat+16*model.emitted) : final.memory query=source.memory query:=
    emitted_prefix source p array model.heap count width query model.index model.emitted emittedInside model.arrayArena blobArena model.heapAligned model.arrayBefore before
  have requestMemory (offset : Nat) (inside : offset<80) : final.memory (rq+BitVec.ofNat 64 offset)=source.memory (rq+BitVec.ofNat 64 offset):=by
    apply earlier
    have number:=byteAddress_toNat rq offset (by have upper:=model.image.cursorArena.upper; omega)
    change (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset at number
    have before:=model.requestBefore
    omega
  have newSlice : EncodedSlice array nextHeap model.heap (count*width+1#64):=
    ⟨by rw [lengthNumber]; omega,by rw [lengthNumber]; omega,⟨lower,by rw [lengthNumber]; omega⟩,model.arrayBefore,by rw [lengthNumber]; omega⟩
  refine {
    index:=model.index+1,emitted:=model.emitted+1,heap:=nextHeap,slices:=slices,
    indexBound:=(by omega),emittedBound:=(by have bounded:=model.emittedBound; omega),
    indexCell:=(by simpa only [emittedState,BitVec.ofNat_add] using bind_lookup_same _ "i" (BitVec.ofNat 64 model.index+1#64)),
    emittedCell:=(by simpa only [BitVec.ofNat_add] using emitted_count_cell source p array model.heap count width model.index model.emitted),
    requestCell:=(emitted_keeps source p array model.heap count width model.index model.emitted "rq" (by decide) (by decide) (by decide)).trans model.requestCell,
    arrayCell:=(emitted_keeps source p array model.heap count width model.index model.emitted "arr" (by decide) (by decide) (by decide)).trans model.arrayCell,
    installed:=model.installed,domain:=model.domain,little:=model.little,
    image:=model.image.of_memory (by intro index inside; exact ⟨requestMemory (16*index) (by omega),requestMemory (16*index+8) (by omega)⟩),
    heapCell:=heapCell,heapBound:=guards.2.2.2.1,heapAligned:=guards.2.2.2.2,
    arrayArena:=model.arrayArena,arrayAligned:=model.arrayAligned,requestBefore:=model.requestBefore,
    arrayBefore:=(by have before:=model.arrayBefore; omega),rows:=?_}
  intro row inside
  by_cases same : row=model.emitted
  · subst row
    simpa only [slices,Function.update_self] using And.intro (emitted_cells source p array model.heap count width model.index model.emitted emittedInside model.arrayArena).1
      (And.intro (emitted_cells source p array model.heap count width model.index model.emitted emittedInside model.arrayArena).2 newSlice)
  · have old : row<model.emitted:=by omega
    obtain ⟨pointerStored,lengthStored,bounds⟩:=model.rows row old
    have numbers:=descriptor_numbers array row (by omega) model.arrayArena
    have pointerFrame:=earlier (array+BitVec.ofNat 64 (16*row)) (by rw [numbers.1]; omega)
    have lengthFrame:=earlier (array+BitVec.ofNat 64 (16*row+8)) (by rw [numbers.2]; omega)
    have retained : EncodedSlice array nextHeap (model.slices row).1 (model.slices row).2:=
      ⟨bounds.positive,bounds.bounded,bounds.arena,bounds.afterArray,by have before:=bounds.beforeHeap; omega⟩
    simpa [slices,Function.update,same,Ne.symm same] using And.intro (pointerFrame.trans pointerStored) (And.intro (lengthFrame.trans lengthStored) retained)

/-- Inspect the actual empty/nonempty branch and its final increment to
construct the next real model. Its globals and all earlier input cells
come from the same execution, including the allocator's checked room. -/
theorem LoopModel.after_sizes_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index))))
    (cntCell : source.locals.lookup (ofString "cnt")=some (.val (.word (counts model.index))))
    (szCell : source.locals.lookup (ofString "sz")=some (.val (.word (Requests.elementSize model.index))))
    (normal : evaluateHOLFiniteState source afterSizes=(none,target)) :
    ∃ next : LoopModel input target pointer rq array start size counts,next.index=model.index+1 ∧
      model.heap.toNat≤next.heap.toNat ∧ HeapGlobals source target ∧
      ∀ query : BitVec 64,query.toNat<array.toNat→ target.memory query=source.memory query := by
  rw [after_sizes_shape] at normal
  obtain ⟨afterChoice,choiceRun,incrementRun⟩:=sequence_none source target nonemptyChoice incrementIndex normal
  have summary:=(choice_preserves (ofString "i") (by decide) (by decide)).summary_full source
  unfold LocalSummary at summary
  rw [choiceRun] at summary
  have iAfter : afterChoice.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 model.index))):=(summary.1 rfl).trans model.indexCell
  have advancedRead : eval afterChoice (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 model.index+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,iAfter,valueIsWord,valueWord,wordOpHOL,wordOp]
  have targetEq:=assign_none afterChoice target "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 model.index+1#64) advancedRead incrementRun
  by_cases empty : counts model.index=0#64
  · have chosen : evaluateHOLFiniteState source nonemptyChoice=(none,source):=by
      rw [blob_shape.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,cntCell,empty,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have choiceEq:=congrArg Prod.snd (choiceRun.symm.trans chosen)
    change afterChoice=source at choiceEq
    rw [choiceEq] at targetEq
    rw [targetEq]
    exact ⟨model.skip_next active,rfl,Nat.le_refl _,fun key other=>rfl,fun query before=>rfl⟩
  · have chosen : evaluateHOLFiniteState source nonemptyChoice=evaluateHOLFiniteState source blobBody:=by
      rw [blob_shape.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,cntCell,empty,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨room,choiceEq⟩:=model.blob_normal active pCell cntCell szCell (chosen.symm.trans choiceRun)
    rw [choiceEq] at targetEq
    change target=emittedState source (pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index)
      array model.heap (counts model.index) (Requests.elementSize model.index) model.index model.emitted at targetEq
    rw [targetEq]
    let next:=model.emit_next active room
    let count:=counts model.index
    let width:=Requests.elementSize model.index
    let p:=pointer+BitVec.ofNat 64 start+Requests.offsetWord input start model.index
    have amountNumber : (count*width+8#64).toNat=(count*width).toNat+8:=by
      rw [BitVec.toNat_add_of_lt (by change (count*width).toNat+8<2^64; dsimp only [count,width]; omega)]
      rfl
    have guards:=PersistentAlloc.guards model.heap (count*width+8#64) (by rw [amountNumber]; exact room)
    have grows : model.heap.toNat≤next.heap.toNat:=by
      change model.heap.toNat≤(PersistentAlloc.rounded model.heap (count*width+8#64)).toNat
      have bounded:=guards.2.2.1
      omega
    have globals:=congrArg PanSemStateFiniteExact.globals (emitted_metadata source p array model.heap count width model.index model.emitted)
    change (emittedState source p array model.heap count width model.index model.emitted).globals=
      source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded model.heap (count*width+8#64)))) at globals
    have heapFrame : HeapGlobals source (emittedState source p array model.heap count width model.index model.emitted):=by
      intro key other
      rw [globals]
      simp [HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
    have lower : 2701131776≤model.heap.toNat:=by have first:=model.arrayArena.lower; have before:=model.arrayBefore; omega
    have blobArena : AllocatedBytes.Arena model.heap ((count*width).toNat+8):=⟨lower,by omega⟩
    refine ⟨next,rfl,grows,heapFrame,?_⟩
    intro query before
    exact emitted_prefix source p array model.heap count width query model.index model.emitted (by have bounded:=model.emittedBound; omega)
      model.arrayArena blobArena model.heapAligned model.arrayBefore (by omega)

/-- The same genuinely normal complete iteration supplies its actual
next model and one-step counter progress, with heap/global/earlier-memory
frames. All field and blob scopes are restored by that real caller. -/
theorem LoopModel.iteration_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (active : model.index<5)
    (normal : evaluateHOLFiniteState source iterationBody=(none,target)) :
    ∃ next : LoopModel input target pointer rq array start size counts,next.index=model.index+1 ∧
      model.heap.toNat≤next.heap.toNat ∧ HeapGlobals source target ∧
      ∀ query : BitVec 64,query.toNat<array.toNat→ target.memory query=source.memory query := by
  let prepared:=preparedState input source pointer start model.index counts
  let inner:=(evaluateHOLFiniteState prepared afterSizes).2
  have observed:=model.iteration_observe active
  rw [normal] at observed
  have resultEq:=congrArg (fun observation=>observation.1.1) observed
  change none=(evaluateHOLFiniteState prepared afterSizes).1 at resultEq
  have continued : evaluateHOLFiniteState prepared afterSizes=(none,inner):=Prod.ext resultEq.symm rfl
  have frame:=congrArg Prod.snd observed
  change LocalEffects.erase target=LocalEffects.erase inner at frame
  have locals (key : MlS) (notPointer : key≠ofString "p") (notCount : key≠ofString "cnt") (notSize : key≠ofString "sz") :
      target.locals.lookup key=inner.locals.lookup key:=by
    have same:=model.iteration_local active key notPointer notCount notSize
    rw [normal] at same
    exact same
  have cells:=prepared_cells input source pointer start model.index counts
  obtain ⟨next,nextIndex,grows,heapFrame,earlier⟩:=model.prepared.after_sizes_normal active cells.1 cells.2.1 cells.2.2 continued
  let final:=next.of_frame frame
    ((locals _ (by decide) (by decide) (by decide)).trans next.indexCell)
    ((locals _ (by decide) (by decide) (by decide)).trans next.emittedCell)
    ((locals _ (by decide) (by decide) (by decide)).trans next.requestCell)
    ((locals _ (by decide) (by decide) (by decide)).trans next.arrayCell)
  have targetGlobals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=inner.globals at targetGlobals
  have preparedGlobals:=congrArg PanSemStateFiniteExact.globals (prepared_frame input source pointer start model.index counts)
  change prepared.globals=source.globals at preparedGlobals
  have globals : HeapGlobals source target:=by
    intro key other
    rw [targetGlobals]
    exact (heapFrame key other).trans (congrArg (fun table=>table.lookup key) preparedGlobals)
  have memory:=LocalEffects.memory_of_erase inner target frame
  have oldMemory:=LocalEffects.memory_of_erase source prepared (prepared_frame input source pointer start model.index counts)
  exact ⟨final,nextIndex,grows,globals,fun query before=>(congrFun memory query).trans ((earlier query before).trans (congrFun oldMemory query))⟩

set_option maxRecDepth 100000 in
theorem iteration_request_local : LocalPrefix (ofString "rq") iterationBody := by
  simp only [iterationBody,requestsLoopAndReturn,afterArrayAllocation,body,
    Guest.Software.guestFn_encode_execution_requests,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply LocalPrefix.dec
    | apply LocalPrefix.decCall
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | exact LocalPrefix.store _ _
    | exact LocalPrefix.storeByte _ _
    | exact LocalPrefix.skip
    | apply LocalPrefix.assign
    | exact LocalPrefix.call none _ _ (by simp)
    | decide

def loopRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=5-(CounterFlow.counterWord source (ofString "i")).toNat

theorem LoopModel.rank {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) : loopRank source=5-model.index := by
  have number : (BitVec.ofNat 64 model.index).toNat=model.index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bounded:=model.indexBound; omega)]
  simp [loopRank,CounterFlow.counterWord,model.indexCell,valueWord,number]

theorem LoopModel.active_of_test {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (word : BitVec 64)
    (read : eval source loopTest=some (.val (.word word))) (nonzero : word≠0#64) : model.index<5 := by
  by_contra inactive
  have expected:=model.test_read
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- Every outcome of the original repeated request loop has a fixed finite
allowance. Its progress premise is discharged only by that same actual
continuing body, which supplies the next physical row/image model. -/
theorem LoopModel.loop_cost_ranked {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) :
    source.clock-(evaluateHOLFiniteState source (.while loopTest iterationBody)).2.clock≤31456890*loopRank source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel input current pointer rq array start size counts)
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) iterationBody).2.clock≤31456889:=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    exact (live.clocked (current.clock-1)).iteration_uniform (live.active_of_test word read nonzero)
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→ word≠0#64→
      0<loopRank current ∧ (current.clock≠0→ let output:=evaluateHOLFiniteState (decClockHOLFinite current) iterationBody
        (output.1=none ∨ output.1=some .continue)→ invariant output.2 ∧ loopRank output.2<loopRank current):=by
    intro current codeEq valid word read nonzero
    obtain ⟨live⟩:=valid
    have active:=live.active_of_test word read nonzero
    have before:=live.rank
    refine ⟨by rw [before]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iterationBody
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_request_local.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iterationBody=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,grows,globals,memory⟩:=(live.clocked (current.clock-1)).iteration_normal active run
    change next.index=live.index+1 at indexEq
    have after:=next.rank
    exact ⟨⟨next⟩,by rw [before,after,indexEq]; omega⟩
  exact ClockCost.ranked_loop_current source.code loopTest iterationBody 31456889 invariant loopRank priced progress source rfl ⟨model⟩

theorem LoopModel.loop_uniform {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) :
    source.clock-(evaluateHOLFiniteState source (.while loopTest iterationBody)).2.clock≤157284450 := by
  have price:=model.loop_cost_ranked
  rw [model.rank] at price
  omega

/-- Complete unchanged execution-request encoder780, on every actual
outcome from its main-derived entry: setup, all five possible lists and
its original tuple return. This is a source-clock bound, not target steps. -/
theorem body_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤157284452 := by
  let output:=evaluateHOLFiniteState source body
  have run : evaluateHOLFiniteState source (CallPrefix.program setupActions requestsLoopAndReturn)=(output.1,output.2):=by
    rw [←setup_shape]
  rcases CallPrefix.priced_trace source output.2 setupActions requestsLoopAndReturn 2
      (setup_cost source.code entry.installed source rfl) output.1 run with stopped|reached
  · change source.clock-output.2.clock≤157284452
    have price:=stopped.1
    omega
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    obtain ⟨model,indexEq,emittedEq,heapEq,memoryEq⟩:=setup_model entry execution
    have tailPrice:=ClockCost.sequence_current current (.while loopTest iterationBody) loopReturn 157284450 0 model.loop_uniform
      (ClockCost.returned current.code (.rstruct [localVar "arr",localVar "n"]))
    rw [←loop_shape,continued] at tailPrice
    change current.clock-inner.clock≤157284450 at tailPrice
    change source.clock-output.2.clock≤157284452
    omega

/-- The actual normal loop exit has visited all five types and contains
exactly its emitted row prefix. Heap growth, other globals and all earlier
memory are derived from those same normal iterations. -/
theorem LoopModel.loop_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts)
    (normal : evaluateHOLFiniteState source (.while loopTest iterationBody)=(none,post)) :
    ∃ final : LoopModel input post pointer rq array start size counts,final.index=5 ∧ model.heap.toNat≤final.heap.toNat ∧
      HeapGlobals source post ∧ ∀ query : BitVec 64,query.toNat<array.toNat→ post.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel input current pointer rq array start size counts,
    model.heap.toNat≤live.heap.toNat ∧ HeapGlobals source current ∧
    ∀ query : BitVec 64,query.toNat<array.toNat→ current.memory query=source.memory query
  have initial : invariant source:=⟨model,Nat.le_refl _,fun key other=>rfl,fun query before=>rfl⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) iterationBody=(none,target)→ invariant target:=by
    intro current codeEq valid word read nonzero funded target bodyRun
    obtain ⟨live,priorGrowth,globals,memory⟩:=valid
    obtain ⟨next,indexEq,grows,nextGlobals,nextMemory⟩:=(live.clocked (current.clock-1)).iteration_normal (live.active_of_test word read nonzero) bodyRun
    exact ⟨next,Nat.le_trans priorGrowth grows,fun key other=>(nextGlobals key other).trans (globals key other),
      fun query before=>(nextMemory query before).trans (memory query before)⟩
  obtain ⟨final,grows,globals,memory⟩:=loop_invariant_no_control source.code loopTest iterationBody
    (fun current=>(iteration_request_local.summary_full current).2.2) invariant step source post rfl initial normal
  have exited:=loop_normal_exit loopTest iterationBody (fun current=>(iteration_request_local.summary_full current).2.2.1) source post normal
  have expected:=final.test_read
  have finished : final.index=5:=by
    by_cases active : final.index<5
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · have bounded:=final.indexBound
      omega
  exact ⟨final,finished,grows,globals,memory⟩

/-- Physical result of the actual encoder, without its retired local
loop variables. This is the input image needed by request hashing. -/
structure Returned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64)
    (count : Nat) (slices : Nat→BitVec 64×BitVec 64) : Prop where
  countBound : count≤5
  arrayArena : AllocatedBytes.Arena array 80
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+80≤heap.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  rows : ∀ row<count,source.memory (array+BitVec.ofNat 64 (16*row))=.word (slices row).1 ∧
    source.memory (array+BitVec.ofNat 64 (16*row+8))=.word (slices row).2 ∧ EncodedSlice array heap (slices row).1 (slices row).2

theorem Returned.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (data : Returned source array heap count slices)
    (frame : LocalEffects.erase target=LocalEffects.erase source) : Returned target array heap count slices := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  refine ⟨data.countBound,data.arrayArena,data.arrayAligned,data.arrayBefore,by rw [globals]; exact data.heapCell,data.heapBound,data.heapAligned,?_⟩
  intro row inside
  obtain ⟨pointerCell,lengthCell,bounds⟩:=data.rows row inside
  exact ⟨(congrFun memory _).trans pointerCell,(congrFun memory _).trans lengthCell,bounds⟩

theorem LoopModel.returned {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq array : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (model : LoopModel input source pointer rq array start size counts) (finished : model.index=5) :
    Returned source array model.heap model.emitted model.slices :=
  ⟨by have bounded:=model.emittedBound; omega,model.arrayArena,model.arrayAligned,model.arrayBefore,
    model.heapCell,model.heapBound,model.heapAligned,model.rows⟩

theorem setup_request_local : LocalPrefix (ofString "rq") (CallPrefix.program setupActions .skip) := by
  unfold setupActions CallPrefix.program
  exact .decCall (ofString "arr") .one (ofString "alloc") setupArguments (by decide)
    (.dec (ofString "n") .one (.const 0#64) (by decide) (.dec (ofString "i") .one (.const 0#64) (by decide) .skip))

/-- The true normal whole encoder returns its actual array/count tuple,
owned emitted rows and checked heap. All preceding caller memory and other
globals survive this same execution; no hash return is assumed. -/
theorem body_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer rq heap : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (entry : Entry input source pointer rq heap start size counts) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ count nextHeap slices,value=.rStruct [.val (.word heap),.val (.word (BitVec.ofNat 64 count))] ∧
      Returned post heap nextHeap count slices ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat→ post.memory query=source.memory query := by
  have never : NoReturn.Never (CallPrefix.program setupActions .skip):=by
    intro F current returned
    exact (setup_request_local.summary_full current).2.1 returned
  have expanded:=normal
  rw [setup_shape] at expanded
  obtain ⟨current,inner,execution,tailRun,clock,metadata⟩:=CallPrefix.normal_frame_trace source post setupActions requestsLoopAndReturn value never expanded
  obtain ⟨model,indexEq,emittedEq,heapEq,memoryEq⟩:=setup_model entry execution
  have setupEq:=(setup_reached entry execution).2
  rw [loop_shape] at tailRun
  obtain ⟨exited,loopRun,returnRun⟩:=sequence_returned current inner (.while loopTest iterationBody) loopReturn value
    (fun returned=>(LocalPrefix.loop loopTest iteration_request_local).summary_full current |>.2.1 returned) tailRun
  obtain ⟨final,finished,grows,loopGlobals,loopMemory⟩:=model.loop_normal loopRun
  obtain ⟨observed,innerEq⟩:=return_normal exited inner (.rstruct [localVar "arr",localVar "n"]) value returnRun
  have expected : eval exited (.rstruct [localVar "arr",localVar "n"])=some (.rStruct [.val (.word heap),.val (.word (BitVec.ofNat 64 final.emitted))]):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,final.arrayCell,final.emittedCell]
  have answer:=Option.some.inj (observed.symm.trans expected)
  rw [innerEq] at metadata
  change LocalEffects.erase post=LocalEffects.erase exited at metadata
  have returned:=(final.returned finished).of_frame metadata
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change post.globals=exited.globals at globals
  have heapFrame : HeapGlobals source post:=by
    intro key other
    rw [globals]
    apply (loopGlobals key other).trans
    rw [setupEq]
    simp [setupState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  have memory:=LocalEffects.memory_of_erase exited post metadata
  exact ⟨final.emitted,final.heap,final.slices,answer,returned,heapFrame,
    fun query before=>(congrFun memory query).trans ((loopMemory query before).trans (congrFun memoryEq query))⟩

theorem retained_header {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : BeforeRequests input source pointer si record gasWord boundary header encoded)
    (data : Data input target pointer si record gasWord boundary)
    (heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) target)
    (saved : ∀ name : String,ofString "reqs"≠ofString name→ target.locals.lookup (ofString name)=source.locals.lookup (ofString name))
    (memory : ∀ query : BitVec 64,query.toNat<header.toNat+248→ target.memory query=source.memory query) :
    BeforeRequests input target pointer si record gasWord boundary header encoded := by
  have cells (offset : Nat) (small : offset≤240) : target.memory (HeaderEncoding.address header offset)=source.memory (HeaderEncoding.address header offset):=by
    apply memory
    have number:=byteAddress_toNat header offset (by have upper:=physical.buffers.ommer.headerArena.upper; omega)
    change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at number
    change (header+BitVec.ofNat 64 offset).toNat<header.toNat+248
    omega
  exact {physical with
    data:=data,heapAfter:=heapAfter,
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.fields field member),
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.optional field member),
    headerCell:=(saved "h" (by decide)).trans physical.headerCell,payloadCell:=(saved "pl" (by decide)).trans physical.payloadCell,
    requestsCell:=(saved "rh" (by decide)).trans physical.requestsCell,balanceCell:=(saved "bh" (by decide)).trans physical.balanceCell,
    sizeCell:=(saved "bl" (by decide)).trans physical.sizeCell}

/-- The literal reached main encoder invocation supplies its true row
array and bounded count at the same hashing continuation. Header/input
facts and hash workspaces are retained using the actual earlier heap. -/
theorem main_encoder_output {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : BeforeRequests input source pointer si record gasWord boundary header encoded)
    (actual : CallPrefix.Reaches source (.scoped (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments) target) :
    ∃ array nextHeap count slices,BeforeRequests input target pointer si record gasWord boundary header encoded ∧
      Returned target array nextHeap count slices ∧
      target.locals.lookup (ofString "reqs")=some (.rStruct [.val (.word array),.val (.word (BitVec.ofNat 64 count))]) ∧
      (headerFrontier header).toNat+16≤array.toNat := by
  obtain ⟨rq,array,start,size,counts,callee,args,called,entry⟩:=main_entry physical.data
  obtain ⟨child,returned,bodyRun,endpoint⟩:=actual.scoped_known (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments
    [.val (.word rq)] body callee resultShape args called
  obtain ⟨count,nextHeap,slices,answer,rows,globals,older⟩:=body_normal entry returned bodyRun
  have returnedRows : Returned target array nextHeap count slices:=by rw [endpoint]; exact rows.of_frame rfl
  have heapFrame : HeapGlobals source target:=by intro key other; rw [endpoint]; exact globals key other
  have fields:=evaluation_fields (callEntryStateHOLFinite source callee) child body (some (.returned returned)) bodyRun
  have domain : target.memaddrs=source.memaddrs:=by rw [endpoint]; exact fields.1
  have endian : target.be=source.be:=by rw [endpoint]; exact fields.2.1
  have code : target.code=source.code:=by rw [endpoint]; exact fields.2.2.2
  have memory (query : BitVec 64) (before : query.toNat<array.toNat) : target.memory query=source.memory query:=by rw [endpoint]; exact older query before
  obtain ⟨oldHeap,oldCell,oldLower,oldBound,oldAligned⟩:=physical.heapAfter
  have oldEq : oldHeap=array:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using oldCell.symm.trans entry.heapCell
  rw [oldEq] at oldLower
  have numbers:=physical.buffers.numbers header
  have heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) target:=
    ⟨nextHeap,returnedRows.heapCell,by have afterArray:=returnedRows.arrayBefore; omega,returnedRows.heapBound,returnedRows.heapAligned⟩
  have heap : NormalHeapEffects.AtLeast (boundary+32) target:=by
    have afterArray:=returnedRows.arrayBefore
    have beforeHeader:=physical.before
    rw [numbers.frontier] at oldLower
    exact ⟨nextHeap,returnedRows.heapCell,by omega,returnedRows.heapBound,returnedRows.heapAligned⟩
  have saved (name : String) (different : ofString "reqs"≠ofString name) : target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [endpoint]
    exact CallNormal.continuation_lookup_other source child "reqs" name returned different
  have retained:=physical.data.of_heap_frame domain endian code heapFrame heap ((saved "si" (by decide)).trans physical.data.siLocal) (by
    intro query lower before
    apply memory
    have beforeHeader:=physical.before
    rw [numbers.frontier] at oldLower
    omega)
  have headerMemory (query : BitVec 64) (before : query.toNat<header.toNat+248) : target.memory query=source.memory query:=by
    apply memory
    rw [numbers.frontier] at oldLower
    omega
  have reqs : target.locals.lookup (ofString "reqs")=some (.rStruct [.val (.word array),.val (.word (BitVec.ofNat 64 count))]):=by
    rw [endpoint]
    change (CallNormal.continuationEntry source child "reqs" returned).locals.lookup (ofString "reqs")=_
    rw [CallNormal.continuation_lookup_same,answer]
  exact ⟨array,nextHeap,count,slices,retained_header physical retained heapAfter saved headerMemory,returnedRows,reqs,oldLower⟩

def callerActions : List CallPrefix.Action:=[.scoped (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments]

def BeforeHash (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) (header : BitVec 64) (encoded : Nat) : Prop:=
  ∃ array heap count slices,BeforeRequests input source pointer si record gasWord boundary header encoded ∧ Returned source array heap count slices ∧
    source.locals.lookup (ofString "reqs")=some (.rStruct [.val (.word array),.val (.word (BitVec.ofNat 64 count))]) ∧
    (headerFrontier header).toNat+16≤array.toNat

theorem caller_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program callerActions .skip)).2.clock≤157284453 := by
  obtain ⟨rq,heap,start,size,counts,callee,args,called,entry⟩:=main_entry data
  exact ClockCost.scoped_current source (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments [.val (.word rq)]
    body .skip callee resultShape 157284452 0 args called (body_cost entry) (ClockCost.skip source.code)

/-- The actual main encoder caller either stops within its full allowance
or reaches its unchanged hashing continuation with the real row result,
retained headers/input and zero transaction/withdrawal facts. -/
theorem to_after_encoder {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : BeforeRequests input source pointer si record gasWord boundary header encoded)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source PayloadHeaderWithdrawals.afterRoot=(outcome,post)) :
    (source.clock-post.clock≤157284453 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,BeforeHash input current pointer si record gasWord boundary header encoded ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤157284453 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current afterEncode=(outcome,inner) := by
  have expanded:=actual
  rw [caller_shape] at expanded
  change evaluateHOLFiniteState source (CallPrefix.program callerActions afterEncode)=(outcome,post) at expanded
  rcases CallPrefix.priced_trace source post callerActions afterEncode 157284453 (caller_cost physical.data) outcome expanded with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value returned
    have safe : LocalPrefix (ofString "si") (CallPrefix.program callerActions .skip):=
      .decCall (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments (by decide) .skip
    apply (safe.summary_full source).2.1 value
    rw [←stopped.2]
    exact returned
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    have called : CallPrefix.Reaches source (.scoped (ofString "reqs") resultShape (ofString "encode_execution_requests") arguments) current:=by
      cases execution with
      | step first next=>cases next; exact first
    exact Or.inr ⟨current,inner,main_encoder_output physical called,forward,price,endpoint,continued⟩

/-- Complete original payload-header trace to its real request-hash caller,
with every earlier stopped alternative and complete physical hash inputs. -/
theorem to_before_hash {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤476364417764 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,BeforeHash input current pointer si record gasWord boundary header encoded ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤476364417764 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current afterEncode=(outcome,inner) := by
  rcases PayloadHeaderWithdrawals.to_before_requests data checked outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,outer,encoded,physical,forward,price,endpoint,remaining⟩:=reached
    rcases to_after_encoder physical outcome remaining with stopped|reached
    · exact Or.inl ⟨by have cost:=stopped.1; rw [endpoint]; omega,stopped.2⟩
    · obtain ⟨current,inner,ready,nextForward,nextPrice,nextEndpoint,continued⟩:=reached
      exact Or.inr ⟨header,current,inner,encoded,ready,Nat.le_trans nextForward forward,by omega,endpoint.trans nextEndpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.list_bytes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.list_size_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.main_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.Entry.input_before_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.Entry.list_before_heap

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.caller_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_selected
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_frame

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.iteration_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.loop_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.field_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.fields_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.after_sizes_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.iteration_advance

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.size_continue

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.test_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.of_frame

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_args
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_reached

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.fields_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.fields_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.iteration_observe
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.prepared_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.prepared_clock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.prepared_keeps
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.prepared
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.prepared_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.blob_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.blob_copy_args
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.after_blob_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.blob_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.iteration_uniform

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.iteration_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.tag_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.after_blob_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_numbers
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.descriptor_prefix
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.copy_after_tag_away
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.after_blob_metadata
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.after_blob_prefix

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.blob_allocation_args
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.blob_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.choice_preserves
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.increment_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.skip_next

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.emitted_metadata
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.emitted_keeps
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.emitted_count_cell
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.emitted_prefix
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.emitted_cells

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.emit_next

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.after_sizes_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.iteration_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.iteration_request_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.rank
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.active_of_test
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.loop_cost_ranked
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.loop_uniform

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.Returned.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.LoopModel.returned
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.setup_request_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.body_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.retained_header
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.main_encoder_output

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.caller_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.to_after_encoder
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.to_before_hash

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

namespace Code
inductive Routine where | stateInit | block | finish | hash

def declaration : Routine→Decl (BitVec 64)
  | .stateInit=>Guest.Software.guestFn_sha256_state_init
  | .block=>Guest.Software.guestFn_sha256_block
  | .finish=>Guest.Software.guestFn_sha256_finish
  | .hash=>Guest.Software.guestFn_sha256

def entry (routine : Routine):=GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name (routine : Routine):=(entry routine).1
def formals (routine : Routine):=(entry routine).2.1
def body (routine : Routine):=(entry routine).2.2.1
def shape (routine : Routine):=(entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine)=some (formals routine,body routine,shape routine) := by
  cases routine with
  | stateInit=>exact OriginalCode.indexed code installed 84 (entry .stateInit) (by rfl)
  | block=>exact OriginalCode.indexed code installed 85 (entry .block) (by rfl)
  | finish=>exact OriginalCode.indexed code installed 86 (entry .finish) (by rfl)
  | hash=>exact OriginalCode.indexed code installed 87 (entry .hash) (by rfl)
end Code

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem state_supported : StraightBody.accepts (Code.body .stateInit)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem block_supported : StraightBody.accepts (Code.body .block)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

/-- The actual expanded compression has no source calls or loops. Its
large straight-line target work still needs a separate static allowance. -/
theorem state_cost (code) : ClockCost.Bound code (Code.body .stateInit) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "sha_st") code _ state_supported).1

theorem block_cost (code) : ClockCost.Bound code (Code.body .block) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "sha_st") code _ block_supported).1

theorem state_globals (key : MlS) (code) : GlobalEffects.Preserves key code (Code.body .stateInit) :=
  (StraightBody.effects key code _ state_supported).2

theorem block_globals (key : MlS) (code) : GlobalEffects.Preserves key code (Code.body .block) :=
  (StraightBody.effects key code _ block_supported).2

namespace WordFrame

def scalar : ExpHOL 64→Bool
  | .const _ | .op _ _ | .shift _ _ _=>true
  | _=>false

theorem scalar_length (expression : ExpHOL 64) (checked : scalar expression=true)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (read : eval source expression=some value) : (flattenHOL value).length≤1 := by
  cases expression with
  | const word=>
    have actual : eval source (.const word)=some (.val (.word word)):=rfl
    have same:=Option.some.inj (read.symm.trans actual)
    rw [same]
    simp [flattenHOL]
  | op operator arguments=>rw [op_length source operator arguments value read]
  | shift operator left right=>rw [MemoryAt.shift_length source operator left right value read]
  | _=>simp only [scalar] at checked; cases checked

/-- Successful scalar stores touch one word; every failed store leaves
memory unchanged. This includes actual read/mapping failures. -/
theorem scalar_store_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (address expression : ExpHOL 64) (pointer query : BitVec 64)
    (read : eval source address=some (.val (.word pointer)))
    (small : ∀ value,eval source expression=some value→ (flattenHOL value).length≤1)
    (away : query≠pointer) : (evaluateHOLFiniteState source (.store address expression)).2.memory query=source.memory query := by
  by_cases normal : (evaluateHOLFiniteState source (.store address expression)).1=none
  · exact MemoryAt.scalar_store_normal source _ address expression pointer query read small away (Prod.ext normal rfl)
  · classical
    simp only [eval] at read
    rw [evaluateHOLFiniteState_store,read] at normal ⊢
    dsimp only at normal ⊢
    cases valueRead : evalHOLExact source.toExact expression with
    | none=>simp [valueRead]
    | some value=>
      simp only [valueRead] at normal ⊢
      cases stored : panMemStoresHOL pointer (flattenHOL value) source.memaddrs source.memory with
      | none=>simp [stored]
      | some memory=>simp [stored] at normal

def accepts (key : MlS) (size : Nat) : ProgHOL 64→Bool
  | .skip | .return _=>true
  | .assign .local name _=>decide (name≠key)
  | .store address expression=>match ByteOutputFrame.offset? key address with
    | some offset=>decide (offset.toNat<size) && scalar expression
    | none=>false
  | .seq first second=>accepts key size first && accepts key size second
  | .dec name _ _ body=>decide (name≠key) && accepts key size body
  | _=>false

/-- Reuse the checked straight-prefix composition rules, with scalar
word stores in place of byte stores. No successful body run is supplied. -/
theorem sound (key : MlS) (size : Nat) (program : ProgHOL 64) (checked : accepts key size program=true)
    (pointer query : BitVec 64) (away : ∀ offset : Nat,offset<size→ query≠pointer+BitVec.ofNat 64 offset) :
    ByteOutputFrame.Frame key pointer query program := by
  cases program with
  | skip=>exact ByteOutputFrame.sound key 0 .skip rfl pointer query (by intro offset inside; omega)
  | «return» expression=>exact ByteOutputFrame.sound key 0 (.return expression) rfl pointer query (by intro offset inside; omega)
  | assign kind name expression=>
    cases kind with
    | «global»=>cases checked
    | «local»=>exact ByteOutputFrame.sound key 0 (.assign .local name expression) checked pointer query (by intro offset inside; omega)
  | store address expression=>
    unfold accepts at checked
    cases found : ByteOutputFrame.offset? key address with
    | none=>simp only [found] at checked; cases checked
    | some offset=>
      have parts : offset.toNat<size ∧ scalar expression=true:=by
        simpa only [found,Bool.and_eq_true,decide_eq_true_eq] using checked
      intro source cell
      have read:=ByteOutputFrame.offset_sound key address offset found source pointer cell
      have outside : query≠pointer+offset:=by
        simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using away offset.toNat parts.1
      refine ⟨scalar_store_current source address expression (pointer+offset) query read (fun value evaluated=>scalar_length expression parts.2 source value evaluated) outside,?_⟩
      have locals : (evaluateHOLFiniteState source (.store address expression)).2.locals=source.locals:=by
        rw [evaluateHOLFiniteState_store]
        repeat first | rfl | split
      intro normal
      rw [locals]
      exact cell
  | seq first second=>
    have parts : accepts key size first=true ∧ accepts key size second=true:=by simpa only [accepts,Bool.and_eq_true] using checked
    exact ByteOutputFrame.sequence key pointer query first second (sound key size first parts.1 pointer query away) (sound key size second parts.2 pointer query away)
  | dec name shape expression body=>
    have parts : name≠key ∧ accepts key size body=true:=by simpa only [accepts,Bool.and_eq_true,decide_eq_true_eq] using checked
    exact ByteOutputFrame.declared key name pointer query shape expression body parts.1 (sound key size body parts.2 pointer query away)
  | _=>simp only [accepts] at checked; cases checked
termination_by structural program

end WordFrame

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem state_frame_supported : WordFrame.accepts (ofString "stp") 64 (Code.body .stateInit)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem block_frame_supported : WordFrame.accepts (ofString "stp") 64 (Code.body .block)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

theorem state_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (away : ∀ offset : Nat,offset<64→ query≠pointer+BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState source (Code.body .stateInit)).2.memory query=source.memory query :=
  (WordFrame.sound (ofString "stp") 64 (Code.body .stateInit) state_frame_supported pointer query away source cell).1

theorem block_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (away : ∀ offset : Nat,offset<64→ query≠pointer+BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState source (Code.body .block)).2.memory query=source.memory query :=
  (WordFrame.sound (ofString "stp") 64 (Code.body .block) block_frame_supported pointer query away source cell).1

set_option maxRecDepth 100000 in
theorem be32_supported : StraightBody.accepts (CurrentStartup.Code.body .st_be32)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_st_be32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

theorem be32_cost (code) : ClockCost.Bound code (CurrentStartup.Code.body .st_be32) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "p") code _ be32_supported).1

def finishArguments : List (ExpHOL 64):=[.op .add [localVar "out",.panop .mul [localVar "i",.const 4#64]],
  .load .one (.op .add [localVar "stp",.panop .mul [localVar "i",.const 8#64]])]
def finishCall : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") finishArguments
def finishIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def finishIteration : ProgHOL 64:=.seq finishCall finishIncrement
def finishTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 8#64)
def finishTail : ProgHOL 64:=.seq (.while finishTest finishIteration) (.return (.const 0#64))

set_option maxRecDepth 100000 in
theorem finish_shape : Code.body .finish=.dec (ofString "i") .one (.const 0#64) finishTail := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    finishTail,finishTest,finishIteration,finishCall,finishArguments,finishIncrement,localVar]

theorem finish_iteration_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finishIteration 1 := by
  have called:=ClockCost.call_body code (some none) (ofString "st_be32") finishArguments
    (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32) 0
    (CurrentStartup.Code.installed code installed .st_be32) (be32_cost code)
  exact ClockCost.sequence code finishCall finishIncrement 1 0 called (ClockCost.assign code (ofString "i") _)

theorem finish_iteration_advance : CounterFlow.Advances (ofString "i") 1 finishIteration :=
  CounterFlow.sequence (ofString "i") finishCall finishIncrement 0 1
    (CounterFlow.preserved _ _ (.call none _ _ (by simp))) (CounterFlow.increment _)

theorem finish_iteration_local : LocalPrefix (ofString "stp") finishIteration :=
  .seq (.call none _ _ (by simp)) (.assign (ofString "i") _ (by decide))

/-- Every real digest-output outcome costs at most eight loop ticks plus
eight literal st_be32 calls. Failed reads and exhausted clocks are included. -/
theorem finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (Code.body .finish) 16 := by
  intro source codeEq
  have currentInstalled : OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  rw [finish_shape]
  apply ClockCost.declared_value_current source (ofString "i") .one (.const 0#64) (.val (.word 0#64)) finishTail 16 rfl
  let entered:=bind source "i" 0#64
  have loopPrice:=CounterFlow.constant_loop_cost source.code (ofString "i") (ofString "stp") finishIteration 1 8 (by decide)
    (finish_iteration_cost source.code currentInstalled) finish_iteration_advance finish_iteration_local entered 0#64 rfl (bind_lookup_same _ _ _) (by decide)
  exact ClockCost.sequence_current entered (.while finishTest finishIteration) (.return (.const 0#64)) 16 0 loopPrice (ClockCost.returned source.code (.const 0#64))

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Code.installed
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_globals

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.scalar_length
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.scalar_store_current
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.sound
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_memory

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_cost

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def blockArguments : List (ExpHOL 64):=[.var .global (ofString "sha_st"),.op .add [localVar "p",localVar "i"]]
def blockCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_block") blockArguments
def blockIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 64#64])
def blockIteration : ProgHOL 64:=.seq blockCall blockIncrement
def blockTest : ExpHOL 64:=.cmp .notLower (localVar "len") (.op .add [localVar "i",.const 64#64])
def blocks : ProgHOL 64:=.while blockTest blockIteration

theorem block_iteration_local : LocalPrefix (ofString "len") blockIteration :=
  .seq (.call none _ _ (by simp)) (.assign (ofString "i") _ (by decide))

theorem block_iteration_advance : CounterFlow.Advances (ofString "i") 64 blockIteration :=
  CounterFlow.sequence (ofString "i") blockCall blockIncrement 0 64
    (CounterFlow.preserved _ _ (.call none _ _ (by simp))) (CounterFlow.increment_by _ 64)

theorem block_iteration_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code blockIteration 1 := by
  have called:=ClockCost.call_body code (some none) (ofString "sha256_block") blockArguments
    (Code.formals .block) (Code.body .block) (Code.shape .block) 0
    (Code.installed code installed .block) (block_cost code)
  exact ClockCost.sequence code blockCall blockIncrement 1 0 called (ClockCost.assign code (ofString "i") _)

theorem block_test_reads (length : Nat) (small : length+64<2^64) :
    CounterFlow.NamedStride.Reads (ofString "len") blockTest 64 length := by
  intro source word counter count bounded
  have encoded : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sum : (word+64#64).toNat=word.toNat+64:=by
    rw [BitVec.toNat_add_of_lt (by change word.toNat+64<2^64; omega)]; rfl
  by_cases active : word.toNat+64≤length
  · have lower : ¬BitVec.ofNat 64 length<word+64#64:=by change ¬(BitVec.ofNat 64 length).toNat<(word+64#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,blockTest,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]
  · have lower : BitVec.ofNat 64 length<word+64#64:=by change (BitVec.ofNat 64 length).toNat<(word+64#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,blockTest,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]

/-- Actual block calls and loop ticks, including failures. Expanded compression
work is accounted for separately when translating to target steps. -/
theorem blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source) :
    source.clock-(evaluateHOLFiniteState source blocks).2.clock≤2*(length/64) := by
  have priced:=CounterFlow.NamedStride.loop_cost (ofString "len") source.code blockTest blockIteration 64 length 1 (by decide) (by omega)
    block_iteration_advance block_iteration_local.summary_full (block_test_reads length small) (block_iteration_cost source.code installed) source rfl valid
  exact Nat.le_trans priced (Nat.mul_le_mul_left 2 (Nat.div_le_div_right (Nat.sub_le _ _)))

/-- The normally completed real loop supplies its own short padding remainder. -/
theorem blocks_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) :
    ∃ word,post.locals.lookup (ofString "i")=some (.val (.word word)) ∧
      post.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length ∧ length-word.toNat<64 := by
  have next:=CounterFlow.NamedStride.loop_normal (ofString "len") source.code blockTest blockIteration 64 length (by decide) (by omega)
    block_iteration_advance block_iteration_local.summary_full (block_test_reads length small) source post rfl valid normal
  obtain ⟨word,counter,count,bounded⟩:=next
  have ended:=loop_normal_exit blockTest blockIteration (fun current=>(block_iteration_local.summary_full current).2.2.1) source post normal
  have read:=block_test_reads length small post word counter count bounded
  have inactive : ¬word.toNat+64≤length:=by
    intro active
    rw [if_pos active] at read
    have contradiction:=ended.symm.trans read
    cases contradiction
  exact ⟨word,counter,count,bounded,by omega⟩

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_test_reads
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_normal

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def state : ExpHOL 64:=.var .global (ofString "sha_st")
def pad : ExpHOL 64:=.var .global (ofString "sha_pad")
def remainder : ExpHOL 64:=.op .sub [localVar "len",localVar "i"]
def zeroPad : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [pad,.const 128#64]
def copyPad : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") [pad,.op .add [localVar "p",localVar "i"],localVar "rem"]
def padFirst : ProgHOL 64:=.storeByte (.op .add [pad,localVar "rem"]) (.const 128#64)
def selectTotal : ProgHOL 64:=.ite (.cmp .notLower (localVar "rem") (.const 56#64))
  (.assign .local (ofString "total") (.const 128#64)) .skip
def storeLength : ProgHOL 64:=.call (some (none,none)) (ofString "st_be64")
  [.op .sub [.op .add [pad,localVar "total"],.const 8#64],.shift .lsl (localVar "len") (.const 3#64)]
def absorbPad : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_block") [state,pad]
def extraPad : ProgHOL 64:=.ite (.cmp .equal (localVar "total") (.const 128#64))
  (.call (some (none,none)) (ofString "sha256_block") [state,.op .add [pad,.const 64#64]]) .skip
def digestCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_finish") [state,localVar "out"]
def finalTail : ProgHOL 64:=.seq selectTotal (.seq storeLength (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64))))))
def paddingFinish : ProgHOL 64:=.seq padFirst (.dec (ofString "total") .one (.const 64#64) finalTail)
def paddingTail : ProgHOL 64:=.seq zeroPad (.seq copyPad paddingFinish)
def afterBlocks : ProgHOL 64:=.dec (ofString "rem") .one remainder paddingTail
def initCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_state_init") [state]

set_option maxRecDepth 100000 in
theorem hash_shape : Code.body .hash=.seq initCall (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks)) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    initCall,state,blocks,blockTest,blockIteration,blockCall,blockArguments,blockIncrement,afterBlocks,remainder,paddingTail,
    zeroPad,copyPad,paddingFinish,padFirst,pad,finalTail,selectTotal,storeLength,absorbPad,extraPad,digestCall,localVar]

set_option maxRecDepth 100000 in
theorem bswap_supported : StraightBody.accepts (CurrentStartup.Code.body .bswap64)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  rfl

set_option maxRecDepth 100000 in
/-- Current aligned bswap and two-BE32 fallback paths, including failures. -/
theorem be64_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (CurrentStartup.Code.body .st_be64) 3 := by
  have swap : ClockCost.Bound code (CurrentStartup.Code.body .bswap64) 0:=
    ClockCost.of_quiet code _ (StraightBody.effects (ofString "x") code _ bswap_supported).1
  have be32 (args : List (ExpHOL 64)) : ClockCost.Bound code (.call (some (none,none)) (ofString "st_be32") args) 1:=
    ClockCost.call_body code (some none) (ofString "st_be32") args
      (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32) 0
      (CurrentStartup.Code.installed code installed .st_be32) (be32_cost code)
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  refine ClockCost.sequence code _ _ 1 2 ?_ ?_
  · apply ClockCost.conditional code _ _ _ 1 0
    · apply ClockCost.scoped_body code _ _ (ofString "bswap64") _ _
        (CurrentStartup.Code.formals .bswap64) (CurrentStartup.Code.body .bswap64) (CurrentStartup.Code.shape .bswap64) 0 0
        (CurrentStartup.Code.installed code installed .bswap64) swap
      exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.returned code _)
    · exact ClockCost.skip code
  · exact ClockCost.sequence code _ _ 1 1 (be32 _) (ClockCost.sequence code _ _ 1 0 (be32 _) (ClockCost.returned code _))

theorem compression_call_cost (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "sha256_block") args) 1 :=
  ClockCost.call_body code (some none) (ofString "sha256_block") args
    (Code.formals .block) (Code.body .block) (Code.shape .block) 0 (Code.installed code installed .block) (block_cost code)

theorem final_tail_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finalTail 23 := by
  have digest:=ClockCost.call_body code (some none) (ofString "sha256_finish") [state,localVar "out"]
    (Code.formals .finish) (Code.body .finish) (Code.shape .finish) 16 (Code.installed code installed .finish) (finish_cost code installed)
  have last : ClockCost.Bound code (.seq digestCall (.return (.const 0#64))) 17:=
    ClockCost.sequence code _ _ 17 0 digest (ClockCost.returned code _)
  have extra : ClockCost.Bound code extraPad 1:=by
    simpa only [extraPad,Nat.max_zero] using ClockCost.conditional code _ _ _ 1 0
      (compression_call_cost code installed _) (ClockCost.skip code)
  have two : ClockCost.Bound code (.seq extraPad (.seq digestCall (.return (.const 0#64)))) 18:=
    ClockCost.sequence code _ _ 1 17 extra last
  have three : ClockCost.Bound code (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64))))) 19:=
    ClockCost.sequence code _ _ 1 18 (compression_call_cost code installed _) two
  have stored:=ClockCost.call_body code (some none) (ofString "st_be64")
    [.op .sub [.op .add [pad,localVar "total"],.const 8#64],.shift .lsl (localVar "len") (.const 3#64)]
    (CurrentStartup.Code.formals .st_be64) (CurrentStartup.Code.body .st_be64) (CurrentStartup.Code.shape .st_be64) 3
    (CurrentStartup.Code.installed code installed .st_be64) (be64_cost code installed)
  have four : ClockCost.Bound code (.seq storeLength (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64)))))) 23:=
    ClockCost.sequence code _ _ 4 19 stored three
  have select : ClockCost.Bound code selectTotal 0:=ClockCost.conditional code _ _ _ 0 0
    (ClockCost.assign code (ofString "total") _) (ClockCost.skip code)
  exact ClockCost.sequence code _ _ 0 23 select four

theorem padding_finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code paddingFinish 23 := by
  have tail:=ClockCost.declared code (ofString "total") .one (.const 64#64) finalTail 23 (final_tail_cost code installed)
  exact ClockCost.sequence code _ _ 0 23 (ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)) tail

/-- The genuine short remainder suffices, including invalid pointer/read/store
outcomes. Neither memory mapping nor a later successful hash is assumed. -/
theorem padding_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rem : Nat)
    (small : rem<64) (installed : OriginalCode.Installed source.code)
    (remCell : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))) :
    source.clock-(evaluateHOLFiniteState source paddingTail).2.clock≤267 := by
  have zero:=BufferDynamicCost.zero_cost source pad (.const 128#64) 128 installed (by decide) rfl
  have zeroPrice : source.clock-(evaluateHOLFiniteState source zeroPad).2.clock≤165:=zero
  apply ClockCost.sequence_reached_current source zeroPad _ 165 102 zeroPrice
  intro middle normal
  have codeEq:=(evaluation_fields source middle zeroPad none normal).2.2.2
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
  have nextRem : middle.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=
    (CallNormal.ignored_lookup source middle (ofString "rem") (ofString "memzero") [pad,.const 128#64] normal).trans remCell
  have remRead : eval middle (localVar "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=by
    simp [eval,evalHOLExact,toExact,localVar,nextRem]
  have copy:=BufferDynamicCost.copy_cost middle pad (.op .add [localVar "p",localVar "i"]) (localVar "rem") rem
    nextInstalled (by omega) remRead
  have copyBound : CopyAny.price rem+1≤79:=by unfold CopyAny.price; omega
  have copyPrice : middle.clock-(evaluateHOLFiniteState middle copyPad).2.clock≤79:=Nat.le_trans copy copyBound
  exact ClockCost.sequence_current middle copyPad paddingFinish 79 23 copyPrice (padding_finish_cost middle.code nextInstalled)

theorem after_blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (word : BitVec 64)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (count : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (bounded : word.toNat≤length) (short : length-word.toNat<64) :
    source.clock-(evaluateHOLFiniteState source afterBlocks).2.clock≤267 := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : BitVec.ofNat 64 length-word=BitVec.ofNat 64 (length-word.toNat):=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change word.toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact bounded),number,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have read : eval source remainder=some (.val (.word (BitVec.ofNat 64 (length-word.toNat)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,remainder,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  exact ClockCost.declared_current source "rem" remainder (BitVec.ofNat 64 (length-word.toNat)) paddingTail 267 read
    (padding_cost (QueryBranch.bind source "rem" (BitVec.ofNat 64 (length-word.toNat))) (length-word.toNat) short installed (bind_lookup_same _ _ _))

def bodyPrice (length : Nat) : Nat:=2*(length/64)+268

theorem loop_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source) :
    source.clock-(evaluateHOLFiniteState source (.seq blocks afterBlocks)).2.clock≤2*(length/64)+267 := by
  apply ClockCost.sequence_reached_current source blocks afterBlocks (2*(length/64)) 267 (blocks_cost source length small installed valid)
  intro middle normal
  obtain ⟨word,counter,count,bounded,short⟩:=blocks_normal source middle length small valid normal
  have sameCode:=(evaluation_fields source middle blocks none normal).2.2.2
  exact after_blocks_cost middle length word small (by rw [sameCode]; exact installed) counter count bounded short

/-- Complete unchanged general SHA on every outcome. This prices source
calls/loop ticks; expanded straight-line target work remains separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (Code.body .hash)).2.clock≤bodyPrice length := by
  rw [hash_shape]
  have initial:=ClockCost.call_body source.code (some none) (ofString "sha256_state_init") [state]
    (Code.formals .stateInit) (Code.body .stateInit) (Code.shape .stateInit) 0 (Code.installed source.code installed .stateInit) (state_cost source.code)
  have first : source.clock-(evaluateHOLFiniteState source initCall).2.clock≤1:=initial source rfl
  have combined:=ClockCost.sequence_reached_current source initCall _ 1 (2*(length/64)+267) first (by
    intro middle normal
    have nextCount : middle.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
      (CallNormal.ignored_lookup source middle (ofString "len") (ofString "sha256_state_init") [state] normal).trans count
    have sameCode:=(evaluation_fields source middle initCall none normal).2.2.2
    have nextInstalled : OriginalCode.Installed middle.code:=by rw [sameCode]; exact installed
    apply ClockCost.declared_current middle "i" (.const 0#64) 0#64 (.seq blocks afterBlocks) (2*(length/64)+267) rfl
    exact loop_tail_cost (QueryBranch.bind middle "i" 0#64) length small nextInstalled
      ⟨0#64,bind_lookup_same _ _ _,(bind_lookup_other middle "i" "len" 0#64 (by decide)).trans nextCount,by simp⟩)
  have total : 1+(2*(length/64)+267)=bodyPrice length:=by unfold bodyPrice; omega
  rw [total] at combined
  exact combined

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.hash_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.bswap_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.final_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.padding_finish_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.padding_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.after_blocks_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.loop_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def values (pointer out : BitVec 64) (length : Nat) : List (ValueHOL 64):=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 length)),.val (.word out)]
theorem hash_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256")=some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],Code.body .hash,.one) := by
  simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
    using Code.installed code installed .hash

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer out : BitVec 64) (length : Nat)
    (code : codeFn (ofString "sha256")=some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],Code.body .hash,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "sha256") (values pointer out length)=some (Code.body .hash,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) :=
  word_triple_environment codeFn (ofString "sha256") (ofString "p") (ofString "len") (ofString "out")
    (Code.body .hash) .one pointer (BitVec.ofNat 64 length) out (by decide) (by decide) (by decide) code

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat) (small : length+64<2^64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256") arguments)).2.clock≤bodyPrice length+1 := by
  obtain ⟨callee,called,pointerCell,count,outCell⟩:=environment source.code.lookup pointer out length (hash_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "sha256") arguments (values pointer out length) (Code.body .hash) callee .one (bodyPrice length)
    args called (body_cost (callEntryStateHOLFinite source callee) length small installed count)

/-- Price the real size expression alone; failed or ill-typed pointer reads
stop before the body and remain covered by the same allowance. -/
theorem dynamic_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+64<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256") [pointer,size,out])).2.clock≤bodyPrice length+1 := by
  have code:=hash_code source.code installed
  cases pointerRead : eval source pointer with
  | none=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
      simp only [eval] at pointerRead
      simp [evalListHOLFinite,evalListHOLExact,pointerRead]
    rw [evaluateHOLFiniteState_call,args]; simp
  | some pointerValue=>
    cases outRead : eval source out with
    | none=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      rw [evaluateHOLFiniteState_call,args]; simp
    | some outValue=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=
          some [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue]:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      cases called : lookupCodeHOLFinite source.code.lookup (ofString "sha256") [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue] with
      | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp
      | some data=>
        obtain ⟨actual,callee,shape⟩:=data
        obtain ⟨pointerWord,sizeWord,outWord,pointerEq,sizeEq,outEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "sha256")
          (ofString "p") (ofString "len") (ofString "out") (Code.body .hash) actual .one shape code pointerValue (.val (.word (BitVec.ofNat 64 length))) outValue callee called
        rw [pointerEq,outEq] at args
        exact call_cost source [pointer,size,out] pointerWord outWord length small installed args

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.hash_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.dynamic_call_cost

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem be32_globals (key : MlS) (code) : GlobalEffects.Preserves key code (CurrentStartup.Code.body .st_be32) :=
  (StraightBody.effects key code _ be32_supported).2

set_option maxRecDepth 100000 in
theorem be64_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (CurrentStartup.Code.body .st_be64) := by
  have swap : GlobalEffects.Preserves key code (CurrentStartup.Code.body .bswap64):=(StraightBody.effects key code _ bswap_supported).2
  have be32 (args : List (ExpHOL 64)) : GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "st_be32") args):=
    GlobalEffects.call_body key code (some none) (ofString "st_be32") args
      (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32)
      (CurrentStartup.Code.installed code installed .st_be32) (be32_globals key code)
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  apply GlobalEffects.sequence
  · apply GlobalEffects.conditional
    · apply GlobalEffects.scoped_body key code _ _ (ofString "bswap64") _ _
        (CurrentStartup.Code.formals .bswap64) (CurrentStartup.Code.body .bswap64) (CurrentStartup.Code.shape .bswap64)
        (CurrentStartup.Code.installed code installed .bswap64) swap
      exact GlobalEffects.sequence key code _ _ (GlobalEffects.store key code _ _) (GlobalEffects.returned key code _)
    · exact GlobalEffects.skip key code
  · exact GlobalEffects.sequence key code _ _ (be32 _) (GlobalEffects.sequence key code _ _ (be32 _) (GlobalEffects.returned key code _))

theorem finish_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code (Code.body .finish) := by
  rw [finish_shape]
  apply GlobalEffects.declared
  apply GlobalEffects.sequence
  · apply GlobalEffects.loop
    exact GlobalEffects.sequence key code finishCall finishIncrement
      (GlobalEffects.call_body key code (some none) (ofString "st_be32") finishArguments
        (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32)
        (CurrentStartup.Code.installed code installed .st_be32) (be32_globals key code))
      (GlobalEffects.assign key code (ofString "i") _)
  · exact GlobalEffects.returned key code _

theorem compression_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256_block") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256_block") args
    (Code.formals .block) (Code.body .block) (Code.shape .block) (Code.installed code installed .block) (block_globals key code)

theorem digest_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256_finish") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256_finish") args
    (Code.formals .finish) (Code.body .finish) (Code.shape .finish) (Code.installed code installed .finish) (finish_globals key code installed)

theorem final_tail_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code finalTail := by
  unfold finalTail selectTotal storeLength absorbPad extraPad digestCall
  repeat' first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _
    | exact compression_call_globals key code installed _
    | exact digest_call_globals key code installed _
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be64") _
        (CurrentStartup.Code.formals .st_be64) (CurrentStartup.Code.body .st_be64) (CurrentStartup.Code.shape .st_be64)
        (CurrentStartup.Code.installed code installed .st_be64) (be64_globals key code installed)

theorem body_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (Code.body .hash) := by
  rw [hash_shape]
  have padding : GlobalEffects.Preserves key code afterBlocks:=by
    unfold afterBlocks paddingTail paddingFinish zeroPad copyPad padFirst
    repeat' first
      | exact final_tail_globals key code installed
      | apply GlobalEffects.sequence
      | apply GlobalEffects.declared
      | exact GlobalEffects.byte_store key code _ _
      | exact CurrentKeccak.Hash.zero_call_globals key code installed _
      | exact CurrentKeccak.Hash.copy_call_globals key code installed _
  have loop : GlobalEffects.Preserves key code blocks:=GlobalEffects.loop key code blockTest blockIteration
    (GlobalEffects.sequence key code blockCall blockIncrement (compression_call_globals key code installed blockArguments) (GlobalEffects.assign key code (ofString "i") _))
  exact GlobalEffects.sequence key code initCall _
    (GlobalEffects.call_body key code (some none) (ofString "sha256_state_init") [state]
      (Code.formals .stateInit) (Code.body .stateInit) (Code.shape .stateInit) (Code.installed code installed .stateInit) (state_globals key code))
    (GlobalEffects.declared key code (ofString "i") .one (.const 0#64) _ (GlobalEffects.sequence key code blocks afterBlocks loop padding))

theorem call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256") args
    (Code.formals .hash) (Code.body .hash) (Code.shape .hash) (Code.installed code installed .hash) (body_globals key code installed)

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_call_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.final_tail_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.body_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.call_globals

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Use the same actual two-argument lookup to identify the first scalar
formal. The second expression may read the current compression workspace. -/
theorem first_word_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function firstName secondName : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (first second : ExpHOL 64) (pointer query : BitVec 64) (different : firstName≠secondName)
    (code : source.code.lookup function=some ([(firstName,.one),(secondName,.one)],body,shape))
    (read : eval source first=some (.val (.word pointer)))
    (frame : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),∀ target value,
      callee.lookup firstName=some (.val (.word pointer))→
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target)→ target.memory query=source.memory query)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function [first,second])=(none,post)) : post.memory query=source.memory query := by
  classical
  obtain ⟨positive,args,actualBody,callee,actualShape,target,value,arguments,called,bodyRun,checked,endpoint,fields⟩:=
    CallNormal.ignored_data source post function [first,second] actual
  have argsEq : ∃ stored,args=[.val (.word pointer),stored]:=by
    simp only [eval] at read
    change evalListHOLExact source.toExact [first,second]=some args at arguments
    cases valueRead : evalHOLExact source.toExact second with
    | none=>simp [evalListHOLExact,read,valueRead] at arguments
    | some stored=>exact ⟨stored,Option.some.inj (by simpa [evalListHOLExact,read,valueRead] using arguments.symm)⟩
  obtain ⟨stored,rfl⟩:=argsEq
  obtain ⟨bodyEq,binding⟩:=checked_pair_left source.code.lookup function firstName secondName body shape pointer stored different code actualBody callee actualShape called
  rw [bodyEq] at bodyRun
  rw [endpoint]
  exact frame callee target value binding bodyRun

set_option maxRecDepth 100000 in
theorem be32_frame_supported : ByteOutputFrame.accepts (ofString "p") 4 (CurrentStartup.Code.body .st_be32)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  rfl

theorem be32_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source first=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 4)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be32") [first,second])=(none,post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "st_be32")=some ([(ofString "p",.one),(ofString "v",.one)],CurrentStartup.Code.body .st_be32,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be32,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .st_be32
  apply first_word_call_memory source post (ofString "st_be32") (ofString "p") (ofString "v") (CurrentStartup.Code.body .st_be32) .one
    first second pointer query (by decide) code read ?_ normal
  intro callee target value cell run
  have bodyFrame:=(ByteOutputFrame.sound (ofString "p") 4 (CurrentStartup.Code.body .st_be32) be32_frame_supported pointer query
    (fun offset inside=>(away offset inside).2) (callEntryStateHOLFinite source callee) cell).1
  rw [run] at bodyFrame
  exact bodyFrame

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.first_word_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_call_memory

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem finish_other (key : MlS) (different : key≠ofString "i") : LocalPrefix key finishIteration :=
  .seq (.call none _ _ (by simp)) (.assign _ _ different)

theorem finish_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (active : index<8)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away pointer query 32) (run : evaluateHOLFiniteState source finishIteration=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩:=sequence_none source post finishCall finishIncrement run
  let address : ExpHOL 64:=.op .add [localVar "out",.panop .mul [localVar "i",.const 4#64]]
  let expression : ExpHOL 64:=.load .one (.op .add [localVar "stp",.panop .mul [localVar "i",.const 8#64]])
  have read : eval source address=some (.val (.word (pointer+BitVec.ofNat 64 (4*index)))):=by
    simp [eval,address,evalHOLExact,evalListHOLExact,toExact,localVar,output,position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have called:=be32_call_memory source middle address expression (pointer+BitVec.ofNat 64 (4*index)) query installed read
    (CopyGeneral.Away.subrange pointer query 32 (4*index) 4 away (by omega)) normal
  have assigned:=MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans called

theorem finish_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (away : CopyGeneral.Away pointer query 32)
    (run : evaluateHOLFiniteState source (.while finishTest finishIteration)=(none,post)) : post.memory query=source.memory query := by
  have summary:=MemoryAt.constant_loop_normal source.code (ofString "i") (ofString "stp") finishIteration 8 query (by decide)
    finish_iteration_local.summary_full finish_iteration_advance
    (fun current=>current.locals.lookup (ofString "out")=some (.val (.word pointer))) (by intro current actual; exact actual)
    (by intro current codeEq currentOutput index active currentPosition target bodyRun
        have localFrame:=(finish_other (ofString "out") (by decide)).summary_full current
        unfold LocalSummary at localFrame
        rw [bodyRun] at localFrame
        exact ⟨(localFrame.1 rfl).trans currentOutput,finish_step_memory current target pointer query index (codeEq.symm ▸ installed) active currentOutput currentPosition away bodyRun⟩)
    source post 0 rfl output (by decide) position run
  exact summary.2.2

/-- Normal original digest output touches only its32 output bytes. The actual
BE32 calls supply their own successful scalar reads. -/
theorem finish_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (Code.body .finish)=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [finish_shape] at run
  refine MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query finishTail value rfl ?_ run
  intro inner remaining
  let entry:=QueryBranch.bind source "i" 0#64
  have nextOutput : entry.locals.lookup (ofString "out")=some (.val (.word pointer)):=
    (bind_lookup_other source "i" "out" 0#64 (by decide)).trans output
  have safe : LocalPrefix (ofString "out") (.while finishTest finishIteration):=.loop _ (finish_other (ofString "out") (by decide))
  obtain ⟨middle,normal,returned⟩:=sequence_returned entry inner _ (.return (.const 0#64)) value (safe.summary_full entry).2.1 remaining
  have frame:=finish_loop_memory entry middle pointer query installed nextOutput (bind_lookup_same _ _ _) away normal
  have finalFrame:=MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at finalFrame
  exact finalFrame.trans frame

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_other
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_step_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_memory

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem state_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_state_init") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_state_init")=some ([(ofString "stp",.one)],Code.body .stateInit,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_state_init,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .stateInit
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "sha256_state_init") (ofString "stp") (Code.body .stateInit) .one stp code
  apply MemoryAt.call_normal source post (ofString "sha256_state_init") args [.val (.word stp)] (Code.body .stateInit) callee .one query read called ?_ normal
  intro target value run
  have frame:=state_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

set_option maxRecDepth 100000 in
theorem compression_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp),.val (.word blk)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_block")=some ([(ofString "stp",.one),(ofString "blk",.one)],Code.body .block,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_block,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .block
  obtain ⟨callee,called,cell,blockCell⟩:=word_pair_environment source.code.lookup (ofString "sha256_block") (ofString "stp") (ofString "blk")
    (Code.body .block) .one stp blk (by decide) code
  apply MemoryAt.call_normal source post (ofString "sha256_block") args [.val (.word stp),.val (.word blk)] (Code.body .block) callee .one query read called ?_ normal
  intro target value run
  have frame:=block_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

theorem digest_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp),.val (.word out)])
    (away : CopyGeneral.Away out query 32)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_finish") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_finish")=some ([(ofString "stp",.one),(ofString "out",.one)],Code.body .finish,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_finish,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .finish
  obtain ⟨callee,called,stateCell,cell⟩:=word_pair_environment source.code.lookup (ofString "sha256_finish") (ofString "stp") (ofString "out")
    (Code.body .finish) .one stp out (by decide) code
  exact MemoryAt.call_normal source post (ofString "sha256_finish") args [.val (.word stp),.val (.word out)] (Code.body .finish) callee .one query read called
    (fun target value run=>finish_memory (callEntryStateHOLFinite source callee) target out query installed cell away value run) normal

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_call_memory

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
/-- Only the compression-state pointer is needed to frame a normal block
call; its other argument may be any actual successful scalar expression. -/
theorem compression_first_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source first=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") [first,second])=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_block")=some ([(ofString "stp",.one),(ofString "blk",.one)],Code.body .block,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_block,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .block
  apply first_word_call_memory source post (ofString "sha256_block") (ofString "stp") (ofString "blk") (Code.body .block) .one
    first second stp query (by decide) code read ?_ normal
  intro callee target value cell run
  have frame:=block_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

theorem blocks_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code blocks :=
  GlobalEffects.loop key code blockTest blockIteration (GlobalEffects.sequence key code blockCall blockIncrement
    (compression_call_globals key code installed blockArguments) (GlobalEffects.assign key code (ofString "i") _))

/-- Every real normal block loop only writes the64-byte state. No initialized
input block contents, fixed counter, digest value or later success is needed. -/
theorem blocks_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (stateCell : source.globals.lookup (ofString "sha_st")=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) : post.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  apply MemoryAt.loop_normal source.code (ofString "len") blockTest blockIteration query block_iteration_local.summary_full invariant ?_
    source post rfl stateCell normal
  intro current codeEq ready observed read nonzero funded target bodyRun
  change evaluateHOLFiniteState (decClockHOLFinite current) (.seq blockCall blockIncrement)=(none,target) at bodyRun
  have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
  have kept:=(GlobalEffects.sequence (ofString "sha_st") current.code blockCall blockIncrement
    (compression_call_globals (ofString "sha_st") current.code currentInstalled blockArguments) (GlobalEffects.assign (ofString "sha_st") current.code (ofString "i") _))
    (decClockHOLFinite current) rfl
  rw [bodyRun] at kept
  have nextState : invariant target:=(congrArg Prod.snd kept).trans ready
  obtain ⟨middle,front,back⟩:=sequence_none (decClockHOLFinite current) target blockCall blockIncrement bodyRun
  have firstRead : eval (decClockHOLFinite current) (.var .global (ofString "sha_st"))=some (.val (.word stp)):=by
    simpa only [eval,evalHOLExact,toExact,invariant,decClockHOLFinite,decClockHOLExact] using ready
  have frame:=compression_first_memory (decClockHOLFinite current) middle (.var .global (ofString "sha_st")) (.op .add [localVar "p",localVar "i"])
    stp query currentInstalled firstRead away front
  have assigned:=MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 64#64]) query
  change (evaluateHOLFiniteState middle blockIncrement).2.memory query=middle.memory query at assigned
  rw [back] at assigned
  exact ⟨nextState,assigned.trans frame⟩

theorem blocks_local (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS) (different : key≠ofString "i")
    (normal : evaluateHOLFiniteState source blocks=(none,post)) : post.locals.lookup key=source.locals.lookup key :=
  counter_loop_local source post blockTest (ofString "sha256_block") blockArguments "i" (.op .add [localVar "i",.const 64#64]) key different normal

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_first_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_local

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual allocated SHA workspace. No hash value, mapped input read or
future successful call is included. -/
structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  stateGlobal : source.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  padGlobal : source.globals.lookup (ofString "sha_pad")=some (.val (.word pad))
  stateArena : AllocatedBytes.Arena stp 64
  padArena : AllocatedBytes.Arena pad 128
  stateAligned : stp.toNat%8=0
  padAligned : pad.toNat%8=0

theorem Environment.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (same : LocalEffects.erase target=LocalEffects.erase source) : Environment target stp pad := by
  have code:=congrArg PanSemStateFiniteExact.code same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  exact ⟨by rw [code]; exact ready.installed,domain.trans ready.domain,by rw [globals]; exact ready.stateGlobal,
    by rw [globals]; exact ready.padGlobal,ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

theorem Environment.after {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (globals : ∀ key,GlobalEffects.Preserves key source.code program)
    (run : evaluateHOLFiniteState source program=(result,target)) : Environment target stp pad := by
  have fields:=evaluation_fields source target program result run
  have state:=globals (ofString "sha_st") source rfl
  have padding:=globals (ofString "sha_pad") source rfl
  rw [run] at state padding
  exact ⟨by rw [fields.2.2.2]; exact ready.installed,fields.1.trans ready.domain,
    (congrArg Prod.snd state).trans ready.stateGlobal,(congrArg Prod.snd padding).trans ready.padGlobal,
    ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad query : BitVec 64) : Prop where
  environment : Environment target stp pad
  memory : target.memory query=source.memory query
  locals : ∀ key,target.locals.lookup key=source.locals.lookup key

theorem Frame.cell {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad query : BitVec 64}
    (frame : Frame source target stp pad query) (key : MlS) (value : ValueHOL 64)
    (cell : source.locals.lookup key=some value) : target.locals.lookup key=some value := (frame.locals key).trans cell

theorem zero_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (arena : AllocatedBytes.Arena dst length) (aligned : dst.toNat%8=0) (multiple : length%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>CurrentKeccak.Hash.zero_call_globals key source.code environment.installed arguments) run,
   MemoryAt.zero_normal source post arguments dst query length args environment.installed environment.domain arena aligned multiple away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "memzero") arguments run⟩

theorem copy_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad src dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (inputArena : AllocatedBytes.Arena src length) (outArena : AllocatedBytes.Arena dst length) (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>CurrentKeccak.Hash.copy_call_globals key source.code environment.installed arguments) run,
   MemoryAt.copy_normal source post arguments src dst query length args environment.installed environment.domain inputArena outArena away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "memcpy") arguments run⟩

theorem compression_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad blk query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word stp),.val (.word blk)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>compression_call_globals key source.code environment.installed arguments) run,
   compression_call_memory source post stp blk query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "sha256_block") arguments run⟩

theorem byte_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad address query : BitVec 64)
    (environment : Environment source stp pad) (destination expression : ExpHOL 64)
    (read : eval source destination=some (.val (.word address))) (away : query≠panByteAlignHOL (width:=64) address)
    (run : evaluateHOLFiniteState source (.storeByte destination expression)=(none,post)) : Frame source post stp pad query := by
  have frame:=byte_store_normal_frame source post destination expression address read run
  exact ⟨environment.after _ _ (fun key=>GlobalEffects.byte_store key source.code destination expression) run,
    frame.2 query away,by intro key; rw [frame.1]⟩

theorem digest_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad out query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word stp),.val (.word out)])
    (away : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_finish") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>digest_call_globals key source.code environment.installed arguments) run,
   digest_call_memory source post stp out query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "sha256_finish") arguments run⟩

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Environment.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Environment.after
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Frame.cell
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.zero_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.copy_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.byte_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_frame

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def be64Test : ExpHOL 64:=.cmp .equal (.op .and [localVar "p",.const 7#64]) (.const 0#64)
def be64FastTail : ProgHOL 64:=.seq (.store (localVar "p") (localVar "w")) (.return (.const 0#64))
def be64Fast : ProgHOL 64:=.decCall (ofString "w") .one (ofString "bswap64") [localVar "v"] be64FastTail
def be64SlowFirst : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") [localVar "p",.shift .lsr (localVar "v") (.const 32#64)]
def be64SlowSecond : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") [.op .add [localVar "p",.const 4#64],localVar "v"]
def be64Slow : ProgHOL 64:=.seq be64SlowFirst (.seq be64SlowSecond (.return (.const 0#64)))

set_option maxRecDepth 100000 in
theorem be64_shape : CurrentStartup.Code.body .st_be64=.seq (.ite be64Test be64Fast .skip) be64Slow := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    be64Test,be64Fast,be64FastTail,be64Slow,be64SlowFirst,be64SlowSecond,localVar]

set_option maxRecDepth 100000 in
theorem bswap_local (code) : LocalEffects.Preserves code (CurrentStartup.Code.body .bswap64) := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat' first | apply LocalEffects.sequence | exact LocalEffects.assign code _ _ | exact LocalEffects.returned code _

theorem be64_fast_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (vCell : source.locals.lookup (ofString "v")=some (.val (.word input)))
    (away : query≠pointer) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source be64Fast=(some (.returned value),post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "bswap64")=some ([(ofString "x",.one)],CurrentStartup.Code.body .bswap64,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .bswap64
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "bswap64") (ofString "x") (CurrentStartup.Code.body .bswap64) .one input code
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "v"]=some [.val (.word input)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,vCell]
  obtain ⟨funded,target,returned,inner,run,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source post "w" .one (ofString "bswap64")
    [localVar "v"] [.val (.word input)] (CurrentStartup.Code.body .bswap64) be64FastTail callee .one args called value normal
  have typed : shapeOfHOLExact returned=.one:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨word,rfl⟩:=ScalarShape.word returned typed
  have pure:=(bswap_local source.code) (callEntryStateHOLFinite source callee) rfl
  rw [run] at pure
  have memory : target.memory query=source.memory query:=congrFun (LocalEffects.memory_of_erase (callEntryStateHOLFinite source callee) target pure) query
  let entered:=CallNormal.continuationEntry source target "w" (.val (.word word))
  have pointerCell : entered.locals.lookup (ofString "p")=some (.val (.word pointer)):=by
    simpa only [entered,CallNormal.continuationEntry] using
      (MemoryAt.set_lookup_other {target with locals:=source.locals} (ofString "w") (ofString "p") (.val (.word word)) (by decide)).trans pCell
  have wordCell : entered.locals.lookup (ofString "w")=some (.val (.word word)):=by
    simp [entered,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have address : eval entered (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,toExact,localVar,pointerCell]
  have storedValue : eval entered (localVar "w")=some (.val (.word word)):=by simp [eval,evalHOLExact,toExact,localVar,wordCell]
  obtain ⟨middle,stored,finished⟩:=sequence_returned entered inner (.store (localVar "p") (localVar "w")) (.return (.const 0#64)) value
    ((LocalPrefix.store (key:=ofString "p") _ _).summary_full entered).2.1 remaining
  have first:=MemoryAt.scalar_store_normal entered middle (localVar "p") (localVar "w") pointer query address
    (by intro actual read; rw [storedValue] at read; cases read; simp [flattenHOL]) away stored
  have last:=MemoryAt.return_current middle (.const 0#64) query
  rw [finished] at last
  rw [endpoint]
  exact last.trans (first.trans memory)

theorem be64_slow_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 8) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source be64Slow=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "p") be64SlowFirst:=.call none _ _ (by simp)
  obtain ⟨middle,first,remaining⟩:=sequence_returned source post be64SlowFirst _ value (safe.summary_full source).2.1 normal
  have firstRead : eval source (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,toExact,localVar,pCell]
  have firstFrame:=be32_call_memory source middle (localVar "p") (.shift .lsr (localVar "v") (.const 32#64)) pointer query installed firstRead
    (by simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange pointer query 8 0 4 away (by decide)) first
  have nextP : middle.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (CallNormal.ignored_lookup source middle (ofString "p") (ofString "st_be32") [localVar "p",.shift .lsr (localVar "v") (.const 32#64)] first).trans pCell
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [(evaluation_fields source middle be64SlowFirst none first).2.2.2]; exact installed
  have secondSafe : LocalPrefix (ofString "p") be64SlowSecond:=.call none _ _ (by simp)
  obtain ⟨last,second,finished⟩:=sequence_returned middle post be64SlowSecond (.return (.const 0#64)) value (secondSafe.summary_full middle).2.1 remaining
  have secondRead : eval middle (.op .add [localVar "p",.const 4#64])=some (.val (.word (pointer+4#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,nextP,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondFrame:=be32_call_memory middle last (.op .add [localVar "p",.const 4#64]) (localVar "v") (pointer+4#64) query nextInstalled secondRead
    (CopyGeneral.Away.subrange pointer query 8 4 4 away (by decide)) second
  have finalFrame:=MemoryAt.return_current last (.const 0#64) query
  rw [finished] at finalFrame
  exact finalFrame.trans (secondFrame.trans firstFrame)

/-- Both actual writer paths retain every word outside the eight output bytes.
Normal return supplies any successful reads/stores; no mapping is assumed. -/
theorem be64_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (vCell : source.locals.lookup (ofString "v")=some (.val (.word input)))
    (away : CopyGeneral.Away pointer query 8) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (CurrentStartup.Code.body .st_be64)=(some (.returned value),post)) : post.memory query=source.memory query := by
  have test : eval source be64Test=some (.val (.word (if pointer &&& 7#64=0#64 then 1#64 else 0#64))):=by
    by_cases aligned : pointer &&& 7#64=0#64
    all_goals simp [eval,evalHOLExact,evalListHOLExact,toExact,be64Test,localVar,pCell,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
  simp only [eval] at test
  rw [be64_shape] at normal
  by_cases aligned : pointer &&& 7#64=0#64
  · have gate : evaluateHOLFiniteState source (.ite be64Test be64Fast .skip)=evaluateHOLFiniteState source be64Fast:=by
      rw [evaluateHOLFiniteState_ite,test,if_pos aligned]
      simp
    have whole : evaluateHOLFiniteState source (.seq be64Fast be64Slow)=(some (.returned value),post):=by
      rw [evaluateHOLFiniteState_seq_line780]
      rwa [evaluateHOLFiniteState_seq_line780,gate] at normal
    have stops : NoFallthrough be64Fast:=NoFallthrough.scoped _ _ _ _ _ (NoFallthrough.sequence _ _ (NoFallthrough.returned _))
    have actual:=NoFallthrough.returning_prefix source post be64Fast be64Slow stops value whole
    have different : query≠pointer:=by simpa only [byteAddress,BitVec.add_zero] using (away 0 (by decide)).1
    exact be64_fast_memory source post pointer input query installed pCell vCell different value actual
  · have gate : evaluateHOLFiniteState source (.ite be64Test be64Fast .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,test,if_neg aligned]
      simp [evaluateHOLFiniteState_skip]
    rw [StateSteps.next_sequence source source _ _ gate (Nat.le_refl _)] at normal
    exact be64_slow_memory source post pointer query installed pCell away value normal

theorem be64_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer),.val (.word input)])
    (away : CopyGeneral.Away pointer query 8)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be64") arguments)=(none,post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "st_be64")=some ([(ofString "p",.one),(ofString "v",.one)],CurrentStartup.Code.body .st_be64,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .st_be64
  obtain ⟨callee,called,pCell,vCell⟩:=word_pair_environment source.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
    (CurrentStartup.Code.body .st_be64) .one pointer input (by decide) code
  exact MemoryAt.call_normal source post (ofString "st_be64") arguments [.val (.word pointer),.val (.word input)] (CurrentStartup.Code.body .st_be64) callee .one query args called
    (fun target value run=>be64_body_memory (callEntryStateHOLFinite source callee) target pointer input query installed pCell vCell away value run) normal

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.bswap_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_fast_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_slow_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_body_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_call_memory

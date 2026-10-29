import InitECandidate.Solver.Input.CurrentVerify.Withdrawals
import InitECandidate.Solver.Input.StraightBody

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

import InitECandidate.Solver.Input.CurrentVerify.Withdrawals
import InitECandidate.Solver.Input.CurrentVerify.GeneralSha
import InitECandidate.Solver.Input.CallPrefixLocalResult
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.Input.HeapReleaseNormal

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
    (∃ array nextHeap count slices,BeforeRequests input target pointer si record gasWord boundary header encoded ∧
      Returned target array nextHeap count slices ∧
      target.locals.lookup (ofString "reqs")=some (.rStruct [.val (.word array),.val (.word (BitVec.ofNat 64 count))]) ∧
      (headerFrontier header).toNat+16≤array.toNat) ∧ PreservesState source target header := by
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
  refine ⟨⟨array,nextHeap,count,slices,retained_header physical retained heapAfter saved headerMemory,returnedRows,reqs,oldLower⟩,?_⟩
  intro origin frame
  exact frame.after (fun key notHeap _=>heapFrame key notHeap) (fun query _ before=>headerMemory query (by omega))

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
        PreservesState source current header ∧ current.clock≤source.clock ∧ source.clock-current.clock≤157284453 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterEncode=(outcome,inner) := by
  have expanded:=actual
  rw [caller_shape] at expanded
  change evaluateHOLFiniteState source (CallPrefix.program callerActions afterEncode)=(outcome,post) at expanded
  rcases CallPrefix.priced_frame_trace source post callerActions afterEncode 157284453 (caller_cost physical.data) outcome expanded with stopped|reached
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
    obtain ⟨ready,preserved⟩:=main_encoder_output physical called
    exact Or.inr ⟨current,inner,ready,preserved,forward,price,endpoint,continued⟩

/-- Complete original payload-header trace to its real request-hash caller,
with every earlier stopped alternative and complete physical hash inputs. -/
theorem to_before_hash {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤182601094503615208 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,BeforeHash input current pointer si record gasWord boundary header encoded ∧
        StateFrame source current header ∧ current.clock≤source.clock ∧ source.clock-current.clock≤182601094503615208 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterEncode=(outcome,inner) := by
  rcases PayloadHeaderWithdrawals.to_before_requests_state data checked outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,outer,encoded,physical,frame,forward,price,endpoint,remaining⟩:=reached
    rcases to_after_encoder physical outcome remaining with stopped|reached
    · exact Or.inl ⟨by have cost:=stopped.1; rw [endpoint.clock]; omega,stopped.2⟩
    · obtain ⟨current,inner,ready,preserved,nextForward,nextPrice,nextEndpoint,continued⟩:=reached
      exact Or.inr ⟨header,current,inner,encoded,ready,preserved source frame,Nat.le_trans nextForward forward,by omega,endpoint.trans nextEndpoint,continued⟩

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

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- These are the actual startup SHA allocations already retained by the
complete decoded-input/main-prefix contract. -/
theorem Data.general_sha {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) : GeneralSha.Environment source 2701131776#64 2701131840#64 :=
  ⟨data.arena.code,data.arena.domain,data.shaState,data.shaPad,by constructor <;> decide,by constructor <;> decide,by decide,by decide⟩

namespace RequestHash

def body : ProgHOL 64:=match Guest.Software.guestFn_compute_requests_hash with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "arr",.one),(ofString "n",.one),(ofString "out",.one)]
def arguments : List (ExpHOL 64):=[.rfield 0 (localVar "reqs"),.rfield 1 (localVar "reqs"),localVar "rh"]
def caller : ProgHOL 64:=.call (some (none,none)) (ofString "compute_requests_hash") arguments
def afterHash : ProgHOL 64:=match ExecutionRequests.afterEncode with | .seq _ rest=>rest | _=>.skip

def rowAddress : ExpHOL 64:=.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]
def hashArguments : List (ExpHOL 64):=[.load .one rowAddress,.load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]),
  .op .add [localVar "cat",.panop .mul [localVar "i",.const 32#64]]]
def hashCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256") hashArguments
def increment : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def iteration : ProgHOL 64:=.seq hashCall increment
def test : ExpHOL 64:=.cmp .less (localVar "i") (localVar "n")
def loop : ProgHOL 64:=.while test iteration
def digestSize : ExpHOL 64:=.panop .mul [localVar "n",.const 32#64]
def finalArguments : List (ExpHOL 64):=[localVar "cat",digestSize,localVar "out"]
def finalCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256") finalArguments
def releaseCall : ProgHOL 64:=.call (some (none,none)) (ofString "heap_release") [localVar "mark"]
def afterLoop : ProgHOL 64:=.seq finalCall (.seq releaseCall (.return (.const 0#64)))
def allocated : ProgHOL 64:=.dec (ofString "i") .one (.const 0#64) (.seq loop afterLoop)
def allocationArguments : List (ExpHOL 64):=[.op .add [digestSize,.const 8#64]]
def afterMark : ProgHOL 64:=.decCall (ofString "cat") .one (ofString "alloc") allocationArguments allocated

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "compute_requests_hash")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 781 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_compute_requests_hash) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_compute_requests_hash,
    formals,body,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,Guest.Software.guestFn_compute_requests_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterMark,allocationArguments,allocated,loop,test,iteration,hashCall,hashArguments,rowAddress,increment,afterLoop,finalCall,finalArguments,
    digestSize,releaseCall,localVar]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem caller_shape : ExecutionRequests.afterEncode=.seq caller afterHash := by
  simp only [afterHash,ExecutionRequests.afterEncode,PayloadHeaderWithdrawals.afterRoot,PayloadHeaderWithdrawals.afterLoop,
    PayloadHeaderWithdrawals.loopAndAfter,PayloadHeaderWithdrawals.afterArray,PayloadHeaderWithdrawals.afterCount,
    PayloadHeaderEntry.afterTransactionTrie,PayloadHeaderEntry.afterSizeGuard,PayloadHeader.afterLength,
    PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,show ofString "alloc"≠ofString "block_rlp_length" from by decide,
    if_false,if_true,caller,arguments,localVar]

theorem iteration_advance : CounterFlow.Advances (ofString "i") 1 iteration :=
  CounterFlow.sequence (ofString "i") hashCall increment 0 1
    (CounterFlow.preserved _ _ (.call none _ _ (by simp))) (CounterFlow.increment _)

theorem iteration_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key iteration :=
  .seq (.call none _ _ (by simp)) (.assign _ _ different)

end RequestHash
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.general_sha
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.caller_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.iteration_local

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical encoded rows, independently of the current heap pointer after
the hash function's own temporary allocation. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64)
    (count : Nat) (slices : Nat→BitVec 64×BitVec 64) : Prop where
  countBound : count≤5
  arrayArena : AllocatedBytes.Arena array 80
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+80≤heap.toNat
  rows : ∀ row<count,source.memory (array+BitVec.ofNat 64 (16*row))=.word (slices row).1 ∧
    source.memory (array+BitVec.ofNat 64 (16*row+8))=.word (slices row).2 ∧ ExecutionRequests.EncodedSlice array heap (slices row).1 (slices row).2

theorem Image.of_returned {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (rows : ExecutionRequests.Returned source array heap count slices) : Image source array heap count slices :=
  ⟨rows.countBound,rows.arrayArena,rows.arrayAligned,rows.arrayBefore,rows.rows⟩

theorem Image.row_number {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (image : Image source array heap count slices) (row offset : Nat)
    (inside : 16*row+offset<80) : (array+BitVec.ofNat 64 (16*row+offset)).toNat=array.toNat+16*row+offset := by
  have number:=byteAddress_toNat array (16*row+offset) (by have bounded:=image.arrayArena.upper; omega)
  simpa only [byteAddress,Nat.add_assoc] using number

theorem Image.of_prefix {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (image : Image source array heap count slices)
    (frame : ∀ query : BitVec 64,array.toNat≤query.toNat→ query.toNat<heap.toNat→ target.memory query=source.memory query) : Image target array heap count slices := by
  refine ⟨image.countBound,image.arrayArena,image.arrayAligned,image.arrayBefore,?_⟩
  intro row inside
  obtain ⟨pointerCell,lengthCell,owned⟩:=image.rows row inside
  have rowBound : row<5:=by have bound:=image.countBound; omega
  have first:=image.row_number row 0 (by omega)
  have second:=image.row_number row 8 (by omega)
  simp only [Nat.add_zero] at first
  exact ⟨(frame _ (by rw [first]; omega) (by rw [first]; have before:=image.arrayBefore; omega)).trans pointerCell,
    (frame _ (by rw [second]; omega) (by rw [second]; have before:=image.arrayBefore; omega)).trans lengthCell,owned⟩

structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64)
    (count : Nat) (slices : Nat→BitVec 64×BitVec 64) where
  index : Nat
  indexBound : index≤count
  image : Image source array heap count slices
  environment : GeneralSha.Environment source 2701131776#64 2701131840#64
  arrayLower : 2701131968≤array.toNat
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  counter : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  catCell : source.locals.lookup (ofString "cat")=some (.val (.word heap))

/-- Read the real owned length row at the actual loop counter. -/
theorem LoopModel.length_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count) :
    eval source (.load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]))=
      some (.val (.word (slices model.index).2)) := by
  have inside : 16*model.index+8<80:=by have small:=model.image.countBound; omega
  have address : eval source (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64])=
      some (.val (.word (array+BitVec.ofNat 64 (16*model.index+8)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.arrayCell,model.counter,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_add,BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc]
  have mapped:=AllocatedBytes.word_mapped source array 80 (16*model.index+8) model.environment.domain model.image.arrayArena inside model.image.arrayAligned (by omega)
  exact Witness.load_word_read source _ _ _ address mapped (model.image.rows model.index active).2.1

/-- Source ticks for the actual row SHA call and its real increment. Errors
and short clocks are included; no successful hash is supplied. -/
theorem LoopModel.iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤7864489 := by
  have owned:=(model.image.rows model.index active).2.2
  have sizeRead : eval source (.load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]))=
      some (.val (.word (BitVec.ofNat 64 (slices model.index).2.toNat))):=by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using model.length_read active
  have called:=GeneralSha.dynamic_call_cost source (.load .one rowAddress)
    (.load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]))
    (.op .add [localVar "cat",.panop .mul [localVar "i",.const 32#64]]) (slices model.index).2.toNat model.environment.installed
    (by have bound:=owned.bounded; omega) sizeRead
  have allowance : GeneralSha.bodyPrice (slices model.index).2.toNat+1≤7864489:=by
    unfold GeneralSha.bodyPrice
    have bound:=owned.bounded
    omega
  have price : source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤7864489:=Nat.le_trans called allowance
  exact ClockCost.sequence_current source hashCall increment 7864489 0 price (ClockCost.assign source.code (ofString "i") _)

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.Image.of_returned
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.Image.row_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.Image.of_prefix
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.length_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.iteration_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem LoopModel.pointer_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count) :
    eval source (.load .one rowAddress)=some (.val (.word (slices model.index).1)) := by
  have inside : 16*model.index<80:=by have small:=model.image.countBound; omega
  have address : eval source rowAddress=some (.val (.word (array+BitVec.ofNat 64 (16*model.index)))):=by
    simp [eval,rowAddress,evalHOLExact,evalListHOLExact,toExact,localVar,model.arrayCell,model.counter,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,Nat.mul_comm]
  have mapped:=AllocatedBytes.word_mapped source array 80 (16*model.index) model.environment.domain model.image.arrayArena inside model.image.arrayAligned (by omega)
  exact Witness.load_word_read source _ _ _ address mapped (model.image.rows model.index active).1

theorem LoopModel.hash_args {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) hashArguments=
      some (GeneralSha.values (slices model.index).1 (heap+BitVec.ofNat 64 (32*model.index)) (slices model.index).2.toNat) := by
  have pointerRead:=model.pointer_read active
  have sizeRead:=model.length_read active
  have outputRead : eval source (.op .add [localVar "cat",.panop .mul [localVar "i",.const 32#64]])=
      some (.val (.word (heap+BitVec.ofNat 64 (32*model.index)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.catCell,model.counter,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      BitVec.ofNat_mul,Nat.mul_comm]
  simp only [eval] at pointerRead sizeRead outputRead
  simp [hashArguments,GeneralSha.values,evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outputRead,BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- A real completed row hash leaves every earlier non-workspace word alone.
The output address geometry follows from the actual small counter/current heap;
no output read, completed later hash or extra allocation funding is supplied. -/
theorem LoopModel.hash_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count)
    (normal : evaluateHOLFiniteState source hashCall=(none,post)) (query : BitVec 64)
    (above : 2701131968≤query.toNat) (below : query.toNat<heap.toNat) : post.memory query=source.memory query := by
  have owned:=(model.image.rows model.index active).2.2
  have indexBound : model.index<5:=by have bound:=model.image.countBound; omega
  have aboveAway (pointer : BitVec 64) (length : Nat) (arena : AllocatedBytes.Arena pointer length)
      (before : pointer.toNat+length≤query.toNat) : CopyGeneral.Away pointer query length:=by
    intro offset inside
    have number:=byteAddress_toNat pointer offset (by have bound:=arena.upper; omega)
    have backing : (panByteAlignHOL (width:=64) (byteAddress pointer offset)).toNat≤pointer.toNat+offset:=by
      rw [AllocatedBytes.aligned_number,←number]
      omega
    constructor
    · intro same; have equal:=congrArg BitVec.toNat same; rw [number] at equal; omega
    · intro same; have equal:=congrArg BitVec.toNat same; omega
  have stateAway:=aboveAway 2701131776#64 64 model.environment.stateArena (by change 2701131840≤query.toNat; omega)
  have padAway:=aboveAway 2701131840#64 128 model.environment.padArena above
  have heapArena : AllocatedBytes.Arena heap 160:=
    ⟨by have low:=model.arrayLower; have before:=model.image.arrayBefore; omega,by have high:=model.heapBound; omega⟩
  have outputArena : AllocatedBytes.Arena (heap+BitVec.ofNat 64 (32*model.index)) 32:=
    AllocatedBytes.Arena.subrange heap 160 (32*model.index) 32 heapArena (by omega)
  have number : (heap+BitVec.ofNat 64 (32*model.index)).toNat=heap.toNat+32*model.index:=
    byteAddress_toNat heap (32*model.index) (by have high:=model.heapBound; omega)
  have aligned : (heap+BitVec.ofNat 64 (32*model.index)).toNat%8=0:=by rw [number]; have old:=model.heapAligned; omega
  have outAway:=AllocatedBytes.Arena.away_below (heap+BitVec.ofNat 64 (32*model.index)) query 32 outputArena aligned (by rw [number]; omega)
  exact GeneralSha.call_memory source post 2701131776#64 2701131840#64 (slices model.index).1 (heap+BitVec.ofNat 64 (32*model.index)) query
    (slices model.index).2.toNat (by have bound:=owned.bounded; omega) model.environment hashArguments (model.hash_args active) owned.arena
    (fun offset inside=>(stateAway offset inside).1) padAway outAway normal

/-- Normal iteration derives the next physical image and its real increment.
The retained prefix includes every request row and older decoded/header data. -/
theorem LoopModel.iteration_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (active : model.index<count)
    (normal : evaluateHOLFiniteState source iteration=(none,post)) :
    ∃ next : LoopModel post array heap count slices,next.index=model.index+1 ∧
      ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ post.memory query=source.memory query := by
  obtain ⟨hashed,hashRun,incrementRun⟩:=sequence_none source post hashCall increment normal
  have assigned:=LocalEffects.assign hashed.code (ofString "i") (.op .add [localVar "i",.const 1#64]) hashed rfl
  change LocalEffects.erase (evaluateHOLFiniteState hashed increment).2=LocalEffects.erase hashed at assigned
  rw [incrementRun] at assigned
  have memory (query : BitVec 64) (above : 2701131968≤query.toNat) (below : query.toNat<heap.toNat) : post.memory query=source.memory query:=
    (congrFun (LocalEffects.memory_of_erase hashed post assigned) query).trans (model.hash_memory active hashRun query above below)
  have kept (key : MlS) (different : key≠ofString "i") : post.locals.lookup key=source.locals.lookup key:=by
    have summary:=(iteration_local key different).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have counter : post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (model.index+1)))):=by
    simpa only [BitVec.ofNat_add] using iteration_advance source post (BitVec.ofNat 64 model.index) model.counter normal
  have image : Image post array heap count slices:=model.image.of_prefix (fun query lower upper=>memory query (by have low:=model.arrayLower; omega) upper)
  have globals : ∀ key,GlobalEffects.Preserves key source.code iteration:=fun key=>
    GlobalEffects.sequence key source.code hashCall increment (GeneralSha.call_globals key source.code model.environment.installed hashArguments)
      (GlobalEffects.assign key source.code (ofString "i") _)
  have environment:=model.environment.after iteration none globals normal
  refine ⟨⟨model.index+1,by have bound:=model.indexBound; omega,image,environment,model.arrayLower,model.heapBound,model.heapAligned,
    counter,(kept _ (by decide)).trans model.countCell,(kept _ (by decide)).trans model.arrayCell,(kept _ (by decide)).trans model.catCell⟩,rfl,memory⟩

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.pointer_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.hash_args
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.hash_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.iteration_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def LoopModel.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (clock : Nat) :
    LoopModel {source with clock:=clock} array heap count slices :=
  ⟨model.index,model.indexBound,⟨model.image.countBound,model.image.arrayArena,model.image.arrayAligned,model.image.arrayBefore,model.image.rows⟩,
    model.environment.of_frame rfl,model.arrayLower,model.heapBound,model.heapAligned,model.counter,model.countCell,model.arrayCell,model.catCell⟩

def loopRank (count : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=count-(CounterFlow.counterWord source (ofString "i")).toNat

theorem LoopModel.rank {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) : loopRank count source=count-model.index := by
  have number : (BitVec.ofNat 64 model.index).toNat=model.index:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bounded:=model.indexBound; have small:=model.image.countBound; omega)]
  simp [loopRank,CounterFlow.counterWord,model.counter,valueWord,number]

theorem LoopModel.test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) :
    eval source test=some (.val (.word (if model.index<count then 1#64 else 0#64))) := by
  have indexSmall : model.index<9223372036854775808:=by have bound:=model.indexBound; have small:=model.image.countBound; omega
  have countSmall : count<9223372036854775808:=by have small:=model.image.countBound; omega
  have indexNumber : (BitVec.ofNat 64 model.index).toNat=model.index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have countNumber : (BitVec.ofNat 64 count).toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,test,evalHOLExact,toExact,localVar,model.counter,model.countCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,indexNumber,countNumber,indexSmall,countSmall]

theorem LoopModel.active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index<count := by
  apply Classical.byContradiction
  intro inactive
  have expected:=model.test_read
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- Every outcome of the real row loop is priced from its actual invariant.
Only normally continuing row calls must construct a next image. -/
theorem LoopModel.loop_cost_ranked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤7864490*loopRank count source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current array heap count slices)
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) iteration).2.clock≤7864489:=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    exact (live.clocked (current.clock-1)).iteration_cost (live.active_of_test word read nonzero)
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→ word≠0#64→
      0<loopRank count current ∧ (current.clock≠0→ let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
        (output.1=none ∨ output.1=some .continue)→ invariant output.2 ∧ loopRank count output.2<loopRank count current):=by
    intro current codeEq valid word read nonzero
    obtain ⟨live⟩:=valid
    have active:=live.active_of_test word read nonzero
    have before:=live.rank
    refine ⟨by rw [before]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact (((iteration_local (ofString "n") (by decide)).summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,memory⟩:=(live.clocked (current.clock-1)).iteration_normal active run
    change next.index=live.index+1 at indexEq
    have after:=next.rank
    exact ⟨⟨next⟩,by rw [before,after,indexEq]; omega⟩
  exact ClockCost.ranked_loop_current source.code test iteration 7864489 invariant (loopRank count) priced progress source rfl ⟨model⟩

theorem LoopModel.loop_uniform {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤39322450 := by
  have priced:=model.loop_cost_ranked
  rw [model.rank] at priced
  have countBound:=model.image.countBound
  omega

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.rank
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.test_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.active_of_test
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.loop_cost_ranked
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.loop_uniform

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A normally completed actual row loop visits precisely count rows and
retains the complete physical image plus every older non-workspace word. -/
theorem LoopModel.loop_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (model : LoopModel source array heap count slices)
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ final : LoopModel post array heap count slices,final.index=count ∧
      ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ post.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel current array heap count slices,
    ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ current.memory query=source.memory query
  have initial : invariant source:=⟨model,fun query above below=>rfl⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant current→ ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→
      word≠0#64→ current.clock≠0→ ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,target)→ invariant target:=by
    intro current codeEq valid word read nonzero funded target bodyRun
    obtain ⟨live,memory⟩:=valid
    obtain ⟨next,indexEq,nextMemory⟩:=(live.clocked (current.clock-1)).iteration_normal (live.active_of_test word read nonzero) bodyRun
    exact ⟨next,fun query above below=>(nextMemory query above below).trans (memory query above below)⟩
  obtain ⟨final,memory⟩:=loop_invariant_no_control source.code test iteration
    (fun current=>((iteration_local (ofString "n") (by decide)).summary_full current).2.2) invariant step source post rfl initial normal
  have exited:=loop_normal_exit test iteration
    (fun current=>((iteration_local (ofString "n") (by decide)).summary_full current).2.2.1) source post normal
  have expected:=final.test_read
  have finished : final.index=count:=by
    by_cases active : final.index<count
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · have bounded:=final.indexBound
      omega
  exact ⟨final,finished,memory⟩

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.LoopModel.loop_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual arr/n/out ABI, prior encoder return and retained startup workspace.
No temporary allocation room or future hash return is supplied. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap out : BitVec 64)
    (count : Nat) (slices : Nat→BitVec 64×BitVec 64) : Prop where
  requests : ExecutionRequests.Returned source array heap count slices
  environment : GeneralSha.Environment source 2701131776#64 2701131840#64
  arrayLower : 2701131968≤array.toNat
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  outCell : source.locals.lookup (ofString "out")=some (.val (.word out))

def amount (count : Nat) : BitVec 64:=BitVec.ofNat 64 (32*count+8)
def setupActions : List CallPrefix.Action:=[.scoped (ofString "mark") .one (ofString "heap_mark") [],
  .scoped (ofString "cat") .one (ofString "alloc") allocationArguments,.declare (ofString "i") .one (.const 0#64)]
def markState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  QueryBranch.bind {source with clock:=source.clock-1} "mark" heap

def setupState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (count : Nat):=
  let marked:=markState source heap
  QueryBranch.bind (QueryBranch.bind (PersistentAlloc.post {marked with clock:=marked.clock-1} heap (amount count)) "cat" heap) "i" 0#64

theorem setup_shape : body=CallPrefix.program setupActions (.seq loop afterLoop) := by
  rw [body_shape]
  rfl

theorem amount_number (count : Nat) (small : count≤5) : (amount count).toNat=32*count+8 := by
  rw [amount,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem allocation_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (cell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (amount count)) := by
  simp [allocationArguments,digestSize,amount,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_add,BitVec.ofNat_mul,Nat.mul_comm]

set_option maxRecDepth 100000 in
theorem mark_cost (code) : ClockCost.Bound code (CurrentStartup.Code.body .heap_mark) 0 := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_heap_mark,progToHOL,expToHOL]
  exact ClockCost.returned code _

set_option maxRecDepth 100000 in
theorem release_body_cost (code) : ClockCost.Bound code (CurrentStartup.Code.body .heap_release) 0 := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_heap_release,progToHOL,expToHOL]
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.of_quiet code _ (QuietClock.assign_kind code .global (ofString "heap_ptr") _)) (ClockCost.returned code _)

theorem release_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code releaseCall 1 :=
  ClockCost.call_body code (some none) (ofString "heap_release") [localVar "mark"]
    (CurrentStartup.Code.formals .heap_release) (CurrentStartup.Code.body .heap_release) (CurrentStartup.Code.shape .heap_release) 0
    (CurrentStartup.Code.installed code installed .heap_release) (release_body_cost code)

/-- Covers the allocator's own capacity-failure trap as well as normal setup. -/
theorem setup_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (CallPrefix.program setupActions .skip) 3 := by
  unfold setupActions CallPrefix.program
  apply ClockCost.scoped_body code _ _ (ofString "heap_mark") _ _
    (CurrentStartup.Code.formals .heap_mark) (CurrentStartup.Code.body .heap_mark) (CurrentStartup.Code.shape .heap_mark) 0 2
    (CurrentStartup.Code.installed code installed .heap_mark) (mark_cost code)
  apply PersistentAlloc.scoped_price code installed (tailPrice:=0)
  exact ClockCost.declared code _ _ _ _ _ (ClockCost.skip code)

/-- The actual concatenated digest has at most160bytes; releasing its own
mark and returning cost one additional caller tick on every outcome. -/
theorem after_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count≤5)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    source.clock-(evaluateHOLFiniteState source afterLoop).2.clock≤274 := by
  have sizeRead : eval source digestSize=some (.val (.word (BitVec.ofNat 64 (32*count)))):=by
    simp [eval,digestSize,evalHOLExact,evalListHOLExact,toExact,localVar,cell,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have called:=GeneralSha.dynamic_call_cost source (localVar "cat") digestSize (localVar "out") (32*count) installed (by omega) sizeRead
  have allowance : GeneralSha.bodyPrice (32*count)+1≤273:=by unfold GeneralSha.bodyPrice; omega
  have first : source.clock-(evaluateHOLFiniteState source finalCall).2.clock≤273:=Nat.le_trans called allowance
  exact ClockCost.sequence_current source finalCall (.seq releaseCall (.return (.const 0#64))) 273 1 first
    (ClockCost.sequence source.code releaseCall (.return (.const 0#64)) 1 0 (release_cost source.code installed) (ClockCost.returned source.code _))

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.setup_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.amount_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.allocation_args
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.mark_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.release_body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.release_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.setup_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.after_loop_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
theorem mark_shape : CurrentStartup.Code.body .heap_mark=.return (.var .global (ofString "heap_ptr")) := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_heap_mark,progToHOL,expToHOL]

/-- Same-run setup derives its saved pointer, actual allocation room and
complete reached state. No later row/final digest return is supplied. -/
theorem setup_reached {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap out : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (entry : Entry source array heap out count slices)
    (actual : CallPrefix.Execution source setupActions current) :
    heap.toNat+(32*count+8)≤2952790016 ∧ current=setupState source heap count := by
  change CallPrefix.Execution source (.scoped (ofString "mark") .one (ofString "heap_mark") []::
    [.scoped (ofString "cat") .one (ofString "alloc") allocationArguments,.declare (ofString "i") .one (.const 0#64)]) current at actual
  obtain ⟨marked,markReached,rest⟩:=actual.head
  have markCode : source.code.lookup (ofString "heap_mark")=some ([],CurrentStartup.Code.body .heap_mark,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_heap_mark,List.map_nil,shapeToHOL]
      using CurrentStartup.Code.installed source.code entry.environment.installed .heap_mark
  have raw : lookupCodeHOLExact source.code.lookup (ofString "heap_mark") []=some (CurrentStartup.Code.body .heap_mark,(fun _=>none),.one):=by
    simp [lookupCodeHOLExact,markCode]
  obtain ⟨markCallee,markCalled,markLocals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  obtain ⟨child,returned,bodyRun,endpoint⟩:=markReached.scoped_known (ofString "mark") .one (ofString "heap_mark") [] []
    (CurrentStartup.Code.body .heap_mark) markCallee .one rfl markCalled
  rw [mark_shape] at bodyRun
  obtain ⟨read,childEq⟩:=return_normal (callEntryStateHOLFinite source markCallee) child (.var .global (ofString "heap_ptr")) returned bodyRun
  have expected : eval (callEntryStateHOLFinite source markCallee) (.var .global (ofString "heap_ptr"))=some (.val (.word heap)):=by
    simp [eval,evalHOLExact,toExact,callEntryStateHOLFinite,entry.requests.heapCell]
  have answer : returned=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  have markedEq : marked=markState source heap:=by rw [endpoint,answer,childEq]; rfl
  rw [markedEq] at rest
  obtain ⟨allocated,reached,declared⟩:=rest.head
  have markedInstalled : OriginalCode.Installed (markState source heap).code:=entry.environment.installed
  have countCell : (markState source heap).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))):=
    (bind_lookup_other {source with clock:=source.clock-1} "mark" "n" heap (by decide)).trans entry.countCell
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment (markState source heap).code.lookup (amount count)
    (PersistentAlloc.original_code _ markedInstalled)
  obtain ⟨child,returned,bodyRun,endpoint⟩:=reached.scoped_known (ofString "cat") .one (ofString "alloc") allocationArguments
    (PersistentAlloc.values (amount count)) PersistentAlloc.body callee .one (allocation_args _ count countCell) called
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite (markState source heap) callee) child heap (amount count)
    amountCell entry.requests.heapCell entry.requests.heapBound (Trap.original_code _ markedInstalled) returned bodyRun
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=(markState source heap).locals}) frame
  change {child with locals:=(markState source heap).locals}=PersistentAlloc.post
    {markState source heap with clock:=(markState source heap).clock-1} heap (amount count) at callerFrame
  have allocatedEq : allocated=QueryBranch.bind (PersistentAlloc.post
      {markState source heap with clock:=(markState source heap).clock-1} heap (amount count)) "cat" heap:=by
    rw [endpoint,answer,callerFrame]
    rfl
  rw [allocatedEq] at declared
  have afterI:=declared.declare_next (.val (.word 0#64)) (by simp [eval,evalHOLExact])
  have currentEq : current=setupState source heap count:=by cases afterI; rfl
  rw [amount_number count entry.requests.countBound] at room
  exact ⟨room,currentEq⟩

theorem setup_model {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap out : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (entry : Entry source array heap out count slices)
    (actual : CallPrefix.Execution source setupActions current) :
    ∃ model : LoopModel current array heap count slices,model.index=0 ∧ current.memory=source.memory := by
  obtain ⟨room,currentEq⟩:=setup_reached entry actual
  rw [currentEq]
  have image : Image (setupState source heap count) array heap count slices:=
    (Image.of_returned entry.requests).of_prefix (by intros; rfl)
  have stateCell : (setupState source heap count).globals.lookup (ofString "sha_st")=some (.val (.word 2701131776#64)):=by
    simpa [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.environment.stateGlobal
  have padCell : (setupState source heap count).globals.lookup (ofString "sha_pad")=some (.val (.word 2701131840#64)):=by
    simpa [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.environment.padGlobal
  have environment : GeneralSha.Environment (setupState source heap count) 2701131776#64 2701131840#64:=
    ⟨entry.environment.installed,entry.environment.domain,stateCell,padCell,entry.environment.stateArena,entry.environment.padArena,
      entry.environment.stateAligned,entry.environment.padAligned⟩
  have counter : (setupState source heap count).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 0))):=bind_lookup_same _ _ _
  have nCell : (setupState source heap count).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))):=by
    simpa [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.countCell
  have arrayCell : (setupState source heap count).locals.lookup (ofString "arr")=some (.val (.word array)):=by
    simpa [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.arrayCell
  have catCell : (setupState source heap count).locals.lookup (ofString "cat")=some (.val (.word heap)):=by
    simp [setupState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  exact ⟨⟨0,by omega,image,environment,entry.arrayLower,entry.requests.heapBound,entry.requests.heapAligned,counter,nCell,arrayCell,catCell⟩,rfl,rfl⟩

/-- Complete original compute_requests_hash on every outcome from its real
owned encoder image and ABI. Temporary room comes from its own actual alloc. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap out : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (entry : Entry source array heap out count slices) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤39322727 := by
  let output:=evaluateHOLFiniteState source body
  have run : evaluateHOLFiniteState source (CallPrefix.program setupActions (.seq loop afterLoop))=(output.1,output.2):=by rw [←setup_shape]
  rcases CallPrefix.priced_trace source output.2 setupActions (.seq loop afterLoop) 3
      (setup_cost source.code entry.environment.installed source rfl) output.1 run with stopped|reached
  · change source.clock-output.2.clock≤39322727
    have price:=stopped.1
    omega
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    obtain ⟨model,indexEq,memory⟩:=setup_model entry execution
    have tailPrice:=ClockCost.sequence_reached_current current loop afterLoop 39322450 274 model.loop_uniform (by
      intro looped loopRun
      obtain ⟨final,finished,kept⟩:=model.loop_normal loopRun
      exact after_loop_cost looped count final.image.countBound final.environment.installed final.countCell)
    rw [continued] at tailPrice
    change current.clock-inner.clock≤39322724 at tailPrice
    change source.clock-output.2.clock≤39322727
    omega

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.mark_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.setup_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.setup_model
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

def values (array out : BitVec 64) (count : Nat) : List (ValueHOL 64):=
  [.val (.word array),.val (.word (BitVec.ofNat 64 count)),.val (.word out)]

/-- The actual main reqs tuple, header output and physical encoder result
supply this helper's real callee entry. No request-hash return is assumed. -/
theorem main_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : ExecutionRequests.BeforeHash input source pointer si record gasWord boundary header encoded) :
    ∃ array heap count slices callee,
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values array (requestsBase header) count) ∧
      lookupCodeHOLFinite source.code.lookup (ofString "compute_requests_hash") (values array (requestsBase header) count)=some (body,callee,.one) ∧
      Entry (callEntryStateHOLFinite source callee) array heap (requestsBase header) count slices := by
  obtain ⟨array,heap,count,slices,physical,rows,reqs,afterHeader⟩:=ready
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values array (requestsBase header) count):=by
    simp [arguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,reqs,physical.requestsCell]
  obtain ⟨callee,called,arrayCell,countCell,outCell⟩:=word_triple_environment source.code.lookup (ofString "compute_requests_hash")
    (ofString "arr") (ofString "n") (ofString "out") body .one array (BitVec.ofNat 64 count) (requestsBase header)
    (by decide) (by decide) (by decide) (original_code source.code physical.data.arena.code)
  have lower : 2701131968≤array.toNat:=by
    have numbers:=physical.buffers.numbers header
    have headerLower:=physical.buffers.ommer.headerArena.lower
    rw [numbers.frontier] at afterHeader
    omega
  exact ⟨array,heap,count,slices,callee,args,called,rows.of_frame rfl,physical.data.general_sha.of_frame rfl,lower,arrayCell,countCell,outCell⟩

/-- Complete actual main request-hash caller allowance on every outcome. -/
theorem caller_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : ExecutionRequests.BeforeHash input source pointer si record gasWord boundary header encoded) :
    source.clock-(evaluateHOLFiniteState source caller).2.clock≤39322728 := by
  obtain ⟨array,heap,count,slices,callee,args,called,entry⟩:=main_entry ready
  exact ClockCost.call_current source (some none) (ofString "compute_requests_hash") arguments (values array (requestsBase header) count)
    body callee .one 39322727 args called (body_cost entry)

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.main_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.caller_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem arena_away_above (pointer query : BitVec 64) (length : Nat) (arena : AllocatedBytes.Arena pointer length)
    (above : pointer.toNat+length≤query.toNat) : CopyGeneral.Away pointer query length := by
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by have bound:=arena.upper; omega)
  have backing : (panByteAlignHOL (width:=64) (byteAddress pointer offset)).toNat≤pointer.toNat+offset:=by
    rw [AllocatedBytes.aligned_number,←number]
    omega
  constructor
  · intro same; have equal:=congrArg BitVec.toNat same; rw [number] at equal; omega
  · intro same; have equal:=congrArg BitVec.toNat same; omega

theorem loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code loop :=
  GlobalEffects.loop key code test iteration (GlobalEffects.sequence key code hashCall increment
    (GeneralSha.call_globals key code installed hashArguments) (GlobalEffects.assign key code (ofString "i") _))

theorem loop_local (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS) (different : key≠ofString "i")
    (normal : evaluateHOLFiniteState source loop=(none,post)) : post.locals.lookup key=source.locals.lookup key :=
  counter_loop_local source post test (ofString "sha256") hashArguments "i" (.op .add [localVar "i",.const 1#64]) key different normal

theorem setup_local : LocalPrefix (ofString "out") (CallPrefix.program setupActions .skip) := by
  unfold setupActions CallPrefix.program
  exact .decCall (ofString "mark") .one (ofString "heap_mark") [] (by decide)
    (.decCall (ofString "cat") .one (ofString "alloc") allocationArguments (by decide)
      (.dec (ofString "i") .one (.const 0#64) (by decide) .skip))

/-- Actual final digest, release and return restore this invocation's saved
heap. Only actual normal calls supply their own reads and funding. -/
theorem after_loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap currentHeap out : BitVec 64) (count : Nat)
    (environment : GeneralSha.Environment source 2701131776#64 2701131840#64) (small : count≤5)
    (heapLower : 2701131968≤heap.toNat) (room : heap.toNat+(32*count+8)≤2952790016)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word heap)))
    (catCell : source.locals.lookup (ofString "cat")=some (.val (.word heap)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ CopyGeneral.Away out query 32→ post.memory query=source.memory query := by
  obtain ⟨hashed,hashRun,remaining⟩:=sequence_returned source post finalCall _ value
    ((LocalPrefix.call (key:=ofString "mark") none _ _ (by simp)).summary_full source).2.1 normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) finalArguments=some (GeneralSha.values heap out (32*count)):=by
    simp [finalArguments,digestSize,GeneralSha.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,catCell,outCell,countCell,
      valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have globals (key : MlS) : hashed.globals.lookup key=source.globals.lookup key:=by
    have frame:=GeneralSha.call_globals key source.code environment.installed finalArguments source rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState source finalCall).2=GlobalEffects.erase key source at frame
    rw [hashRun] at frame
    exact congrArg Prod.snd frame
  have installed : OriginalCode.Installed hashed.code:=by
    rw [(evaluation_fields source hashed finalCall none hashRun).2.2.2]
    exact environment.installed
  have nextMark : hashed.locals.lookup (ofString "mark")=some (.val (.word heap)):=
    (CallNormal.ignored_lookup source hashed (ofString "mark") (ofString "sha256") finalArguments hashRun).trans saved
  have nextHeap : hashed.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap)):=(globals _).trans heapCell
  obtain ⟨released,releaseRun,returned⟩:=sequence_returned hashed post releaseCall (.return (.const 0#64)) value
    ((LocalPrefix.call (key:=ofString "mark") none _ _ (by simp)).summary_full hashed).2.1 remaining
  have releaseArgs : evalListHOLFinite hashed (h:=fun address=>Classical.propDecidable (hashed.memaddrs address)) [localVar "mark"]=some [.val (.word heap)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nextMark]
  have releaseEq:=HeapScope.release_normal hashed released heap currentHeap [localVar "mark"] releaseArgs nextHeap installed releaseRun
  obtain ⟨read,postEq⟩:=return_normal released post (.const 0#64) value returned
  have answer : value=.val (.word 0#64):=by simpa only [eval,evalHOLExact,Option.some.injEq] using read.symm
  have restored : post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    rw [postEq,releaseEq]
    simp [emptyLocalsHOLFinite,HeapScope.releasePost,HolFiniteMapExact.update,FUPDATE]
  have kept : HeapGlobals source post:=by
    intro key different
    rw [postEq,releaseEq]
    simpa [emptyLocalsHOLFinite,HeapScope.releasePost,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different] using globals key
  refine ⟨answer,restored,kept,?_⟩
  intro query above below outAway
  have stateAway:=arena_away_above 2701131776#64 query 64 environment.stateArena (by change 2701131840≤query.toNat; omega)
  have padAway:=arena_away_above 2701131840#64 query 128 environment.padArena above
  have inputArena : AllocatedBytes.Arena heap (32*count):=⟨by omega,by omega⟩
  have memory:=GeneralSha.call_memory source hashed 2701131776#64 2701131840#64 heap out query (32*count) (by omega) environment finalArguments args inputArena
    (fun offset inside=>(stateAway offset inside).1) padAway outAway hashRun
  rw [postEq,releaseEq]
  exact memory

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.arena_away_above
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.loop_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.loop_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.setup_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.after_loop_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete normally returning helper restores its actual saved heap and
all older non-workspace/non-output memory through its own lexical scopes. -/
theorem body_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array heap out : BitVec 64}
    {count : Nat} {slices : Nat→BitVec 64×BitVec 64} (entry : Entry source array heap out count slices) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ CopyGeneral.Away out query 32→ post.memory query=source.memory query := by
  have never : NoReturn.Never (CallPrefix.program setupActions .skip):=by
    intro F current returned
    exact (setup_local.summary_full current).2.1 returned
  have expanded:=normal
  rw [setup_shape] at expanded
  obtain ⟨current,inner,execution,tailRun,clock,metadata⟩:=CallPrefix.normal_frame_trace source post setupActions (.seq loop afterLoop) value never expanded
  obtain ⟨model,indexEq,memoryEq⟩:=setup_model entry execution
  obtain ⟨room,setupEq⟩:=setup_reached entry execution
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=by
    rw [setupEq]
    simpa [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using entry.outCell
  have currentMark : current.locals.lookup (ofString "mark")=some (.val (.word heap)):=by
    rw [setupEq]
    simp [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (amount count)))):=by
    rw [setupEq]
    simp [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have setupGlobals : HeapGlobals source current:=by
    intro key different
    rw [setupEq]
    simp [setupState,markState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  obtain ⟨looped,loopRun,afterLoop⟩:=sequence_returned current inner loop afterLoop value
    ((LocalPrefix.loop test (iteration_local (ofString "n") (by decide))).summary_full current).2.1 tailRun
  obtain ⟨final,finished,loopMemory⟩:=model.loop_normal loopRun
  have loopGlobals (key : MlS) : looped.globals.lookup key=current.globals.lookup key:=by
    have frame:=loop_globals key current.code model.environment.installed current rfl
    rw [loopRun] at frame
    exact congrArg Prod.snd frame
  have loopHeap : looped.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (amount count)))):=(loopGlobals _).trans currentHeap
  have loopMark : looped.locals.lookup (ofString "mark")=some (.val (.word heap)):=
    (loop_local current looped (ofString "mark") (by decide) loopRun).trans currentMark
  have loopOut : looped.locals.lookup (ofString "out")=some (.val (.word out)):=
    (loop_local current looped (ofString "out") (by decide) loopRun).trans currentOut
  have lower : 2701131968≤heap.toNat:=by have above:=entry.arrayLower; have before:=entry.requests.arrayBefore; omega
  obtain ⟨answer,restored,globals,memory⟩:=after_loop_normal looped inner heap (PersistentAlloc.rounded heap (amount count)) out count
    final.environment entry.requests.countBound lower room loopHeap loopMark final.catCell loopOut final.countCell value afterLoop
  have postGlobals:=congrArg PanSemStateFiniteExact.globals metadata
  change post.globals=inner.globals at postGlobals
  have postMemory:=LocalEffects.memory_of_erase inner post metadata
  refine ⟨answer,by rw [postGlobals]; exact restored,?_,?_⟩
  · intro key different
    rw [postGlobals]
    exact (globals key different).trans ((loopGlobals key).trans (setupGlobals key different))
  · intro query above below away
    exact (congrFun postMemory query).trans ((memory query above below away).trans
      ((loopMemory query above below).trans (congrFun memoryEq query)))

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Same actual three-word call supplies its body return and inherits the
saved heap and protected-memory frame through ordinary caller restoration. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap out : BitVec 64)
    (count : Nat) (slices : Nat→BitVec 64×BitVec 64) (rows : ExecutionRequests.Returned source array heap count slices)
    (environment : GeneralSha.Environment source 2701131776#64 2701131840#64) (lower : 2701131968≤array.toNat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values array out count))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "compute_requests_hash") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701131968≤query.toNat→ query.toNat<heap.toNat→ CopyGeneral.Away out query 32→ post.memory query=source.memory query := by
  obtain ⟨callee,called,arrayCell,countCell,outCell⟩:=word_triple_environment source.code.lookup (ofString "compute_requests_hash")
    (ofString "arr") (ofString "n") (ofString "out") body .one array (BitVec.ofNat 64 count) out
    (by decide) (by decide) (by decide) (original_code source.code environment.installed)
  have entry : Entry (callEntryStateHOLFinite source callee) array heap out count slices:=
    ⟨rows.of_frame rfl,environment.of_frame rfl,lower,arrayCell,countCell,outCell⟩
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=
    CallNormal.ignored_data source post (ofString "compute_requests_hash") arguments normal
  have valuesEq : actualValues=values array out count:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨answer,restored,globals,memory⟩:=body_normal entry returned bodyRun
  rw [endpoint]
  exact ⟨restored,globals,memory⟩

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.call_normal

namespace InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

/-- Retain precisely the existing header cells; lower SHA workspace may change. -/
theorem retained_header_cells {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : BeforeRequests input source pointer si record gasWord boundary header encoded)
    (data : Data input target pointer si record gasWord boundary)
    (heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) target)
    (saved : ∀ name : String,target.locals.lookup (ofString name)=source.locals.lookup (ofString name))
    (cells : ∀ offset : Nat,offset≤240→ target.memory (HeaderEncoding.address header offset)=source.memory (HeaderEncoding.address header offset)) :
    BeforeRequests input target pointer si record gasWord boundary header encoded :=
  {physical with
    data:=data,heapAfter:=heapAfter,
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.fields field member),
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.optional field member),
    headerCell:=(saved "h").trans physical.headerCell,payloadCell:=(saved "pl").trans physical.payloadCell,
    requestsCell:=(saved "rh").trans physical.requestsCell,balanceCell:=(saved "bh").trans physical.balanceCell,
    sizeCell:=(saved "bl").trans physical.sizeCell}

end InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests.retained_header_cells

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

abbrev BeforeBalance:=PayloadHeaderWithdrawals.BeforeRequests

/-- The actual completed main helper restores the saved heap and retains
all decoded/header inputs at the original following BAL hash. -/
theorem caller_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : ExecutionRequests.BeforeHash input source pointer si record gasWord boundary header encoded)
    (normal : evaluateHOLFiniteState source caller=(none,post)) :
    BeforeBalance input post pointer si record gasWord boundary header encoded ∧ PreservesState source post header := by
  obtain ⟨array,heap,count,slices,physical,rows,reqs,afterHeader⟩:=ready
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values array (requestsBase header) count):=by
    simp [arguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,reqs,physical.requestsCell]
  have numbers:=physical.buffers.numbers header
  have arrayLower : 2701131968≤array.toNat:=by
    have lower:=physical.buffers.ommer.headerArena.lower
    rw [numbers.frontier] at afterHeader
    omega
  obtain ⟨heapCell,globals,memory⟩:=call_normal source post array heap (requestsBase header) count slices rows physical.data.general_sha arrayLower arguments args normal
  have saved (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    CallNormal.ignored_lookup source post (ofString name) (ofString "compute_requests_hash") arguments normal
  have fields:=evaluation_fields source post caller none normal
  have heapLower : boundary+32≤heap.toNat:=by
    have before:=physical.before
    have arrayBefore:=rows.arrayBefore
    rw [numbers.frontier] at afterHeader
    omega
  have heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) post:=
    ⟨heap,heapCell,by have before:=rows.arrayBefore; omega,rows.heapBound,rows.heapAligned⟩
  have heapData : NormalHeapEffects.AtLeast (boundary+32) post:=⟨heap,heapCell,heapLower,rows.heapBound,rows.heapAligned⟩
  have requestsAligned : (requestsBase header).toNat%8=0:=by
    rw [numbers.requests]
    have aligned:=physical.buffers.ommer.headerAligned
    omega
  have prior (query : BitVec 64) (below : query.toNat<(requestsBase header).toNat) : CopyGeneral.Away (requestsBase header) query 32:=
    AllocatedBytes.Arena.away_below (requestsBase header) query 32 physical.buffers.requests requestsAligned below
  have retained : Data input post pointer si record gasWord boundary:=physical.data.of_heap_frame fields.1 fields.2.1 fields.2.2.2 globals heapData
    ((saved "si").trans physical.data.siLocal) (by
      intro query lower upper
      apply memory query (by omega) (by omega)
      apply prior
      rw [numbers.requests]
      have before:=physical.before
      omega)
  refine ⟨?_,?_⟩
  · apply ExecutionRequests.retained_header_cells physical retained heapAfter saved
    intro offset inside
    have number : (HeaderEncoding.address header offset).toNat=header.toNat+offset:=by
      exact byteAddress_toNat header offset (by have bounded:=physical.buffers.ommer.headerArena.upper; omega)
    apply memory (HeaderEncoding.address header offset)
    · rw [number]
      have lower:=physical.data.recordInside.1
      have beforeInput:=physical.data.recordInside.2
      have before:=physical.before
      omega
    · rw [number]
      have arrayBefore:=rows.arrayBefore
      rw [numbers.frontier] at afterHeader
      omega
    · apply prior
      rw [number,numbers.requests]
      omega
  · intro origin frame
    apply frame.after (fun key notHeap _=>globals key notHeap)
    intro query lower before
    apply memory query (by omega) (by have arrayBefore:=rows.arrayBefore; rw [numbers.frontier] at afterHeader; omega)
    apply prior
    rw [numbers.requests]
    omega

def callerActions : List CallPrefix.Action:=[.command caller]

theorem prefix_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : ExecutionRequests.BeforeHash input source pointer si record gasWord boundary header encoded) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program callerActions .skip)).2.clock≤39322728 :=
  ClockCost.sequence_current source caller .skip 39322728 0 (caller_cost ready) (ClockCost.skip source.code)

/-- Real request hashing either stops within its whole allowance or reaches
its unchanged BAL continuation with full earlier decoded/header facts. -/
theorem to_after_hash {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : ExecutionRequests.BeforeHash input source pointer si record gasWord boundary header encoded)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source ExecutionRequests.afterEncode=(outcome,post)) :
    (source.clock-post.clock≤39322728 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,BeforeBalance input current pointer si record gasWord boundary header encoded ∧
        PreservesState source current header ∧ current.clock≤source.clock ∧ source.clock-current.clock≤39322728 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterHash=(outcome,inner) := by
  have expanded:=actual
  rw [caller_shape] at expanded
  change evaluateHOLFiniteState source (CallPrefix.program callerActions afterHash)=(outcome,post) at expanded
  rcases CallPrefix.priced_frame_trace source post callerActions afterHash 39322728 (prefix_cost ready) outcome expanded with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value returned
    have safe : LocalPrefix (ofString "si") (CallPrefix.program callerActions .skip):=.seq (.call none _ _ (by simp)) .skip
    apply (safe.summary_full source).2.1 value
    rw [←stopped.2]
    exact returned
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    have run : evaluateHOLFiniteState source caller=(none,current):=by
      cases execution with
      | step first next=>cases next; cases first with | command _ _ run=>exact run
    obtain ⟨retained,preserved⟩:=caller_normal ready run
    exact Or.inr ⟨current,inner,retained,preserved,forward,price,endpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.caller_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.to_after_hash

namespace InitECandidate.Solver.Input.CurrentVerify.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete unchanged payload-header prefix through both tries, encoding
and request hashing, to its actual final BAL hash continuation. -/
theorem to_before_balance {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤182601094542937936 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,BeforeBalance input current pointer si record gasWord boundary header encoded ∧
        PayloadHeaderEntry.StateFrame source current header ∧ current.clock≤source.clock ∧ source.clock-current.clock≤182601094542937936 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterHash=(outcome,inner) := by
  rcases ExecutionRequests.to_before_hash data checked outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,outer,encoded,physical,frame,forward,price,endpoint,remaining⟩:=reached
    rcases to_after_hash physical outcome remaining with stopped|reached
    · exact Or.inl ⟨by have cost:=stopped.1; rw [endpoint.clock]; omega,stopped.2⟩
    · obtain ⟨current,inner,ready,preserved,nextForward,nextPrice,nextEndpoint,continued⟩:=reached
      exact Or.inr ⟨header,current,inner,encoded,ready,preserved source frame,Nat.le_trans nextForward forward,by omega,endpoint.trans nextEndpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.RequestHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.RequestHash.to_before_balance

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real decoder's final offset supplies the actual BAL slice and its
physical input extent. No later hash or successful byte read is assumed. -/
theorem Data.bal_input {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    ∃ bal length,source.memory (record+64#64)=.word bal ∧ source.memory (record+72#64)=.word (BitVec.ofNat 64 length) ∧
      length≤251655056 ∧ AllocatedBytes.Arena bal length := by
  obtain ⟨array,length,start,size,payload,before,countBound,bytesBound⟩:=data.payload
  obtain ⟨count,remaining,division,remainder⟩:=payload.remaining
  obtain ⟨otherArray,otherStart,otherSize,block⟩:=data.block_inputs
  have lengthBound : length≤251655056:=by have inside:=payload.sliceUpper; have bound:=block.inputBound; omega
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have offsetBound : (Payload.offsetWords input 3).toNat≤length:=by
    have bound:=(payload.valid 3 (by decide)).2.1
    rw [number] at bound
    exact bound
  have difference : BitVec.ofNat 64 length-Payload.offsetWords input 3=BitVec.ofNat 64 (length-(Payload.offsetWords input 3).toNat):=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change (Payload.offsetWords input 3).toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact offsetBound),number,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have pointerNumber : (pointer+62#64+Payload.offsetWords input 3).toNat=pointer.toNat+62+(Payload.offsetWords input 3).toNat:=by
    have exactNumber:=byteAddress_toNat pointer (62+(Payload.offsetWords input 3).toNat)
      (by have before:=data.copied.beforeRecord; have upper:=data.recordArena.upper; have inside:=payload.sliceUpper; have minimum:=payload.minimum; omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc,Nat.add_assoc] using exactNumber
  have facts:=remaining.hash_fields
  refine ⟨pointer+62#64+Payload.offsetWords input 3,length-(Payload.offsetWords input 3).toNat,facts.2.2.1,?_,by omega,?_⟩
  · simpa only [difference] using facts.2.2.2
  · constructor
    · rw [pointerNumber]
      have lower:=data.copied.lower
      omega
    · rw [pointerNumber]
      have before:=data.copied.beforeRecord
      have upper:=data.recordArena.upper
      have inside:=payload.sliceUpper
      have minimum:=payload.minimum
      omega

namespace PayloadHeaderBalance
open PayloadHeaderEntry PayloadHeaderWithdrawals

def arguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "pl",.const 64#64]),
  .load .one (.op .add [localVar "pl",.const 72#64]),localVar "bh"]
def caller : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") arguments

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tail_shape : RequestHash.afterHash=.seq caller (.return (localVar "h")) := by
  simp only [RequestHash.afterHash,ExecutionRequests.afterEncode,PayloadHeaderWithdrawals.afterRoot,PayloadHeaderWithdrawals.afterLoop,
    PayloadHeaderWithdrawals.loopAndAfter,PayloadHeaderWithdrawals.afterArray,PayloadHeaderWithdrawals.afterCount,
    PayloadHeaderEntry.afterTransactionTrie,PayloadHeaderEntry.afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,caller,arguments,localVar]

theorem field_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header value : BitVec 64} {boundary encoded : Nat}
    (ready : RequestHash.BeforeBalance input source pointer si record gasWord boundary header encoded) (offset : Nat)
    (inside : offset<136) (aligned : offset%8=0) (cell : source.memory (record+BitVec.ofNat 64 offset)=.word value) :
    eval source (.load .one (.op .add [localVar "pl",.const (BitVec.ofNat 64 offset)]))=some (.val (.word value)) := by
  have address : eval source (.op .add [localVar "pl",.const (BitVec.ofNat 64 offset)])=some (.val (.word (record+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,ready.payloadCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact Witness.load_word_read source _ _ _ address
    (AllocatedBytes.word_mapped source record 136 offset ready.data.arena.domain ready.data.recordArena inside ready.data.recordAligned aligned) cell

/-- Actual BAL size alone prices every Keccak outcome; its pointers need
no successful future read or hash. Input ownership comes from the decoder. -/
theorem caller_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : RequestHash.BeforeBalance input source pointer si record gasWord boundary header encoded) :
    source.clock-(evaluateHOLFiniteState source caller).2.clock≤81418466 := by
  obtain ⟨bal,length,pCell,nCell,bounded,arena⟩:=ready.data.bal_input
  have sizeRead:=field_read ready 72 (by decide) (by decide) nCell
  have called:=CurrentKeccak.Hash.dynamic_call_cost source (.load .one (.op .add [localVar "pl",.const 64#64]))
    (.load .one (.op .add [localVar "pl",.const 72#64])) (localVar "bh") length ready.data.keccak.installed (by omega) sizeRead
  have allowance : CurrentKeccak.Hash.bodyPrice length+1≤81418466:=by unfold CurrentKeccak.Hash.bodyPrice; omega
  exact Nat.le_trans called allowance

theorem tail_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : RequestHash.BeforeBalance input source pointer si record gasWord boundary header encoded) :
    source.clock-(evaluateHOLFiniteState source RequestHash.afterHash).2.clock≤81418466 := by
  rw [tail_shape]
  exact ClockCost.sequence_current source caller (.return (localVar "h")) 81418466 0 (caller_cost ready) (ClockCost.returned source.code _)

/-- Complete unchanged payload_header788 on every outcome from the real
main-derived decoded inputs and earlier actual transaction scan. -/
theorem body_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) :
    source.clock-(evaluateHOLFiniteState source PayloadHeader.body).2.clock≤182601094624356402 := by
  let output:=evaluateHOLFiniteState source PayloadHeader.body
  have actual : evaluateHOLFiniteState source PayloadHeader.body=(output.1,output.2):=rfl
  rcases RequestHash.to_before_balance data checked output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤182601094624356402
    have price:=stopped.1
    omega
  · obtain ⟨header,current,inner,encoded,ready,frame,forward,price,endpoint,continued⟩:=reached
    have tail:=tail_cost ready
    rw [continued] at tail
    change current.clock-inner.clock≤81418466 at tail
    have endpointClock:=endpoint.clock
    change source.clock-output.2.clock≤182601094624356402
    omega

end PayloadHeaderBalance
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.bal_input
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.tail_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.field_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.caller_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

/-- Actual normal BAL hashing retains all earlier decoded/header cells,
with its actual workspace and32-byte header output supplied by the same run. -/
theorem caller_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : RequestHash.BeforeBalance input source pointer si record gasWord boundary header encoded)
    (normal : evaluateHOLFiniteState source caller=(none,post)) :
    RequestHash.BeforeBalance input post pointer si record gasWord boundary header encoded ∧ PreservesState source post header := by
  obtain ⟨bal,length,pCell,nCell,bounded,inputArena⟩:=ready.data.bal_input
  have pointerRead:=field_read ready 64 (by decide) (by decide) pCell
  have sizeRead:=field_read ready 72 (by decide) (by decide) nCell
  have outputRead : eval source (localVar "bh")=some (.val (.word (balanceBase header))):=by
    simp [eval,evalHOLExact,toExact,localVar,ready.balanceCell]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (CurrentKeccak.Hash.values bal (balanceBase header) length):=by
    simp only [eval] at pointerRead sizeRead outputRead
    simp [arguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outputRead]
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key:=by
    have frame:=CurrentKeccak.Hash.call_globals key source.code ready.data.keccak.installed arguments source rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState source caller).2=GlobalEffects.erase key source at frame
    rw [normal] at frame
    exact congrArg Prod.snd frame
  have saved (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    CallNormal.ignored_lookup source post (ofString name) (ofString "keccak256") arguments normal
  have transport (lower : Nat) (heap : NormalHeapEffects.AtLeast lower source) : NormalHeapEffects.AtLeast lower post:=by
    obtain ⟨cursor,cell,above,upper,aligned⟩:=heap
    exact ⟨cursor,(globals _).trans cell,above,upper,aligned⟩
  have numbers:=ready.buffers.numbers header
  have outAligned : (balanceBase header).toNat%8=0:=by
    rw [numbers.balance]
    have aligned:=ready.buffers.ommer.headerAligned
    omega
  have memory (query : BitVec 64) (above : 2701134824≤query.toNat) (below : query.toNat<(balanceBase header).toNat) : post.memory query=source.memory query:=by
    have stateAway:=RequestHash.arena_away_above 2701132160#64 query 200 ready.data.keccak.stateArena (by change 2701132360≤query.toNat; omega)
    have padAway:=RequestHash.arena_away_above 2701132360#64 query 136 ready.data.keccak.padArena (by change 2701132496≤query.toNat; omega)
    have outAway:=AllocatedBytes.Arena.away_below (balanceBase header) query 32 ready.buffers.balance outAligned below
    exact (CurrentKeccak.Hash.call_frame source post 2701132160#64 2701132360#64 bal (balanceBase header) query length ready.data.keccak arguments args
      inputArena ready.buffers.balance stateAway padAway outAway normal).memory
  have fields:=evaluation_fields source post caller none normal
  have data : Data input post pointer si record gasWord boundary:=ready.data.of_heap_frame fields.1 fields.2.1 fields.2.2.2
    (fun key other=>globals key) (transport _ ready.data.heap) ((saved "si").trans ready.data.siLocal) (by
      intro query lower upper
      apply memory query lower
      rw [numbers.balance]
      have before:=ready.before
      omega)
  refine ⟨?_,?_⟩
  · apply ExecutionRequests.retained_header_cells ready data (transport _ ready.heapAfter) saved
    intro offset inside
    have number : (HeaderEncoding.address header offset).toNat=header.toNat+offset:=
      byteAddress_toNat header offset (by have upper:=ready.buffers.ommer.headerArena.upper; omega)
    apply memory (HeaderEncoding.address header offset)
    · rw [number]
      have lower:=ready.data.recordInside.1
      have beforeInput:=ready.data.recordInside.2
      have before:=ready.before
      omega
    · rw [number,numbers.balance]
      omega
  · intro origin frame
    apply frame.after (fun key _ _=>globals key)
    intro query lower before
    apply memory query (by omega)
    rw [numbers.balance]
    omega

/-- Final original return supplies its actual header word and complete
nonlocal scope observation; no local binding is claimed after Return. -/
theorem tail_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (ready : RequestHash.BeforeBalance input source pointer si record gasWord boundary header encoded) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source RequestHash.afterHash=(some (.returned value),post)) :
    ∃ finished,RequestHash.BeforeBalance input finished pointer si record gasWord boundary header encoded ∧
      value=.val (.word header) ∧ CallPrefix.ScopeFrame post finished ∧ PreservesState source post header := by
  rw [tail_shape] at normal
  obtain ⟨finished,hashRun,returned⟩:=sequence_returned source post caller (.return (localVar "h")) value
    ((LocalPrefix.call (key:=ofString "h") none _ _ (by simp)).summary_full source).2.1 normal
  obtain ⟨retained,preserved⟩:=caller_normal ready hashRun
  obtain ⟨read,postEq⟩:=return_normal finished post (localVar "h") value returned
  have expected : eval finished (localVar "h")=some (.val (.word header)):=by
    simp [eval,evalHOLExact,toExact,localVar,retained.headerCell]
  have answer:=Option.some.inj (read.symm.trans expected)
  have clock:=QuietClock.returned finished.code (localVar "h") finished rfl
  have metadata:=LocalEffects.returned finished.code (localVar "h") finished rfl
  rw [returned] at clock metadata
  exact ⟨finished,retained,answer,⟨clock,metadata⟩,fun origin frame=>(preserved origin frame).of_erase metadata⟩

/-- Complete actual normal payload_header return retains the same physical
header/input state through every enclosing lexical scope. -/
theorem body_normal_state {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source PayloadHeader.body=(some (.returned value),post)) :
    ∃ header finished encoded,RequestHash.BeforeBalance input finished pointer si record gasWord boundary header encoded ∧
      value=.val (.word header) ∧ CallPrefix.ScopeFrame post finished ∧ StateFrame source post header := by
  rcases RequestHash.to_before_balance data checked (some (.returned value)) normal with stopped|reached
  · exact False.elim (stopped.2 value rfl)
  · obtain ⟨header,current,inner,encoded,ready,frame,forward,price,endpoint,continued⟩:=reached
    obtain ⟨finished,retained,answer,last,preserved⟩:=tail_normal ready value continued
    exact ⟨header,finished,encoded,retained,answer,endpoint.trans last,(preserved source frame).of_erase endpoint.metadata⟩

/-- Physical/cost-facing projection of the complete state-preserving return. -/
theorem body_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source PayloadHeader.body=(some (.returned value),post)) :
    ∃ header finished encoded,RequestHash.BeforeBalance input finished pointer si record gasWord boundary header encoded ∧
      value=.val (.word header) ∧ CallPrefix.ScopeFrame post finished := by
  obtain ⟨header,finished,encoded,physical,answer,scope,_⟩:=body_normal_state data checked value normal
  exact ⟨header,finished,encoded,physical,answer,scope⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.caller_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.tail_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.body_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBalance.body_normal_state

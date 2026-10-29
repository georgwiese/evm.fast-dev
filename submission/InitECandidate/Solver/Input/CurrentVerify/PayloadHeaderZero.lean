import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderFields

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure HeapFrontier (current : PanSemStateFiniteExact 64 Guest.HostMemory) (header cursor : BitVec 64) : Prop where
  cell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  arena : AllocatedBytes.Arena cursor 0
  bounded : cursor.toNat≤2952790016
  aligned : cursor.toNat%8=0
  afterHeader : header.toNat+248≤cursor.toNat

def allocatedField (current : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (cursor amount : BitVec 64):=
  setVarHOLFinite name (.val (.word cursor)) (PersistentAlloc.post {current with clock:=current.clock-1} cursor amount)

theorem HeapFrontier.of_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header cursor : BitVec 64)
    (frontier : HeapFrontier source header cursor) (same : target.globals=source.globals) : HeapFrontier target header cursor :=
  ⟨by rw [same]; exact frontier.cell,frontier.arena,frontier.bounded,frontier.aligned,frontier.afterHeader⟩

/-- Each reached allocation supplies its own request room and the next
actual bounded frontier, with the real caller's remaining action list. -/
theorem allocate_field (source current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record header cursor amount : BitVec 64) (name : MlS) (rest : List CallPrefix.Action)
    (installed : OriginalCode.Installed source.code) (frame : HeaderFrame source current pointer record header)
    (frontier : HeapFrontier current header cursor)
    (notHeader : name≠ofString "h") (notRaw : name≠ofString "raw") (notPayload : name≠ofString "pl") (notSI : name≠ofString "si")
    (execution : CallPrefix.Execution current (.scoped name .one (ofString "alloc") [.const amount]::rest) target) :
    AllocatedBytes.Arena cursor amount.toNat ∧
      HeaderFrame source (allocatedField current name cursor amount) pointer record header ∧
      HeapFrontier (allocatedField current name cursor amount) header (PersistentAlloc.rounded cursor amount) ∧
      CallPrefix.Execution (allocatedField current name cursor amount) rest target := by
  have actualInstalled : OriginalCode.Installed current.code:=by rw [frame.code]; exact installed
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) [.const amount]=some (PersistentAlloc.values amount):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next name [.const amount] cursor amount rest actualInstalled args frontier.cell frontier.bounded execution
  have growth:=PersistentAlloc.guards cursor amount room
  have grows:=growth.2.2.1
  have before:=frontier.afterHeader
  have nextFrontier : HeapFrontier (allocatedField current name cursor amount) header (PersistentAlloc.rounded cursor amount):=by
    constructor
    · simp [allocatedField,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    · exact ⟨by have lower:=frontier.arena.lower; omega,by have upper:=growth.2.2.2.1; omega⟩
    · exact growth.2.2.2.1
    · exact growth.2.2.2.2
    · omega
  exact ⟨⟨frontier.arena.lower,by omega⟩,frame.allocated source current pointer record header name cursor amount notHeader notRaw notPayload notSI,nextFrontier,next⟩

def scalarFields : List (Nat×Nat):=[(96,80),(104,88),(112,96),(120,104),(128,16),(136,24)]
def afterBeforeZero : List CallPrefix.Action:=afterTransactionRoot.drop 11
def transactionPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  putHeader (allocatedTransactionRoot hashed pointer heap) heap 40 (afterOmmerHeap heap)
def receiptsPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  putHeader (transactionPointerStored hashed pointer heap) heap 48 (pointer+62#64+84#64)
def bloomPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer heap : BitVec 64):=
  putHeader (receiptsPointerStored hashed pointer heap) heap 56 (pointer+62#64+116#64)
def scalarPrefixStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  payloadFieldsStored source record heap (wideZeroStored (bloomPointerStored hashed pointer heap) heap) scalarFields
def beforeZero (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  putHeader (scalarPrefixStored source hashed pointer record heap) heap 144 (pointer+62#64+372#64)

set_option maxRecDepth 100000 in
theorem before_zero_actions : afterTransactionRoot=
    .command (storeField 40 (localVar "txr"))::
    .command (storeField 48 (Scalar.plus (localVar "raw") 84))::
    .command (storeField 56 (Scalar.plus (localVar "raw") 116))::
    .command storeWideZero::
    (payloadFieldActions scalarFields++
      .command (storeField 144 (Scalar.plus (localVar "raw") 372))::afterBeforeZero) := by
  simp only [afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,
    afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterBeforeZero,payloadFieldActions,scalarFields,storeField,headerField,Scalar.plus,payloadField,
    storeWideZero,wideZeroExpression,localVar,List.cons_append,List.nil_append]
  rfl

theorem scalar_fields_valid : ∀ field∈scalarFields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0 := by
  intro field member
  simp only [scalarFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem local_word_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (.val (.word word))) : eval source (localVar name)=some (.val (.word word)) := by
  simp [eval,evalHOLExact,toExact,localVar,cell]

theorem before_zero_from_execution {input : Guest.InputBlob} {source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat) (layout : OmmerLayout heap)
    (frame : HeaderFrame source (allocatedTransactionRoot hashed pointer heap) pointer record heap)
    (execution : CallPrefix.Execution (allocatedTransactionRoot hashed pointer heap) afterTransactionRoot current) :
    HeaderFrame source (beforeZero source hashed pointer record heap) pointer record heap ∧
      CallPrefix.Execution (beforeZero source hashed pointer record heap) afterBeforeZero current := by
  rw [before_zero_actions] at execution
  have txrCell : (allocatedTransactionRoot hashed pointer heap).locals.lookup (ofString "txr")=some (.val (.word (afterOmmerHeap heap))):=
    bind_lookup_same _ _ _
  have first:=store_field_execute (allocatedTransactionRoot hashed pointer heap) heap 40 (afterOmmerHeap heap) (localVar "txr")
    (frame.domain.trans data.arena.domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame.header
    (local_word_read _ "txr" _ txrCell)
  have trace1:=execution.command_known _ _ first
  have frame1:=frame.stored source _ pointer record heap 40 (afterOmmerHeap heap) layout.headerArena (by decide)
  have second:=store_field_execute (transactionPointerStored hashed pointer heap) heap 48 (pointer+62#64+84#64)
    (Scalar.plus (localVar "raw") 84) (frame1.domain.trans data.arena.domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame1.header
    (Scalar.plus_read _ _ _ 84 (local_word_read _ "raw" _ frame1.raw))
  have trace2:=trace1.command_known _ _ second
  have frame2:=frame1.stored source _ pointer record heap 48 (pointer+62#64+84#64) layout.headerArena (by decide)
  have third:=store_field_execute (receiptsPointerStored hashed pointer heap) heap 56 (pointer+62#64+116#64)
    (Scalar.plus (localVar "raw") 116) (frame2.domain.trans data.arena.domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame2.header
    (Scalar.plus_read _ _ _ 116 (local_word_read _ "raw" _ frame2.raw))
  have trace3:=trace2.command_known _ _ third
  have frame3:=frame2.stored source _ pointer record heap 56 (pointer+62#64+116#64) layout.headerArena (by decide)
  have wide:=wide_zero_execute (bloomPointerStored hashed pointer heap) heap (frame3.domain.trans data.arena.domain) layout.headerArena layout.headerAligned frame3.header
  have trace4:=trace3.command_known _ _ wide
  have frame4:=frame3.wide_zero source _ pointer record heap layout.headerArena
  obtain ⟨frame5,trace5⟩:=payload_fields_from_execution data before layout.headerArena layout.headerAligned scalarFields _ scalar_fields_valid frame4 trace4
  have last:=store_field_execute (scalarPrefixStored source hashed pointer record heap) heap 144 (pointer+62#64+372#64)
    (Scalar.plus (localVar "raw") 372) (frame5.domain.trans data.arena.domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame5.header
    (Scalar.plus_read _ _ _ 372 (local_word_read _ "raw" _ frame5.raw))
  exact ⟨frame5.stored source _ pointer record heap 144 _ layout.headerArena (by decide),trace5.command_known _ _ last⟩

def zeroBase (heap : BitVec 64):=PersistentAlloc.rounded (afterOmmerHeap heap) 32#64
def afterZeroAllocation : List CallPrefix.Action:=afterBeforeZero.drop 1
def allocatedZero (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  allocatedField (beforeZero source hashed pointer record heap) (ofString "z8") (zeroBase heap) 8#64

set_option maxRecDepth 100000 in
theorem zero_allocation_action : afterBeforeZero=
    .scoped (ofString "z8") .one (ofString "alloc") [.const 8#64]::afterZeroAllocation := by
  simp only [afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,
    afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterZeroAllocation]
  rfl

theorem before_zero_heap (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) :
    (beforeZero source hashed pointer record heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (zeroBase heap))) := by
  simp [beforeZero,scalarPrefixStored,payloadFieldsStored,scalarFields,wideZeroStored,bloomPointerStored,receiptsPointerStored,
    transactionPointerStored,putHeader,allocatedTransactionRoot,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,zeroBase]

/-- Main's genuine continuing prefix supplies the next zero buffer and
its bounded frontier, including all preceding scalar and pointer stores. -/
theorem zero_allocation {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ boundary+32≤heap.toNat ∧
      OmmerLayout heap ∧ OmmerHashOutput source pointer record heap hashed ∧
      AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧ AllocatedBytes.Arena (zeroBase heap) 8 ∧
      (zeroBase heap).toNat%8=0 ∧ heap.toNat+248≤(zeroBase heap).toNat ∧
      HeaderFrame source (allocatedZero source hashed pointer record heap) pointer record heap ∧
      HeapFrontier (allocatedZero source hashed pointer record heap) heap (PersistentAlloc.rounded (zeroBase heap) 8#64) ∧
      CallPrefix.Execution (allocatedZero source hashed pointer record heap) afterZeroAllocation current := by
  obtain ⟨heap,hashed,cell,before,layout,output,hashedTrace⟩:=ommer_hash data execution
  obtain ⟨room,txArena,txAligned,txBefore,txFrame,txTrace⟩:=transaction_root_from_execution source hashed current pointer record heap layout output hashedTrace
  obtain ⟨frame,trace⟩:=before_zero_from_execution data (by omega) layout txFrame txTrace
  have growth:=PersistentAlloc.guards (afterOmmerHeap heap) 32#64 room
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  have grows:=growth.2.2.1
  change (afterOmmerHeap heap).toNat+32≤(zeroBase heap).toNat at grows
  have frontier : HeapFrontier (beforeZero source hashed pointer record heap) heap (zeroBase heap):=
    ⟨before_zero_heap source hashed pointer record heap,
      ⟨by have lower:=txArena.lower; omega,by have upper:=growth.2.2.2.1; change (zeroBase heap).toNat≤2952790016 at upper; omega⟩,
      growth.2.2.2.1,growth.2.2.2.2,by omega⟩
  rw [zero_allocation_action] at trace
  obtain ⟨zeroArena,zeroFrame,zeroFrontier,next⟩:=allocate_field source _ current pointer record heap (zeroBase heap) 8#64 (ofString "z8") _
    data.arena.code frame frontier (by decide) (by decide) (by decide) (by decide) trace
  exact ⟨heap,hashed,cell,before,layout,output,txArena,zeroArena,frontier.aligned,frontier.afterHeader,zeroFrame,zeroFrontier,next⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeapFrontier.of_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.allocate_field
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.before_zero_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.scalar_fields_valid
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.local_word_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.before_zero_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.zero_allocation_action
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.before_zero_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.zero_allocation

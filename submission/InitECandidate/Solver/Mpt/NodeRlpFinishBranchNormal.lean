import InitECandidate.Solver.Mpt.NodeRlpFinishBranchCost
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.CurrentRlp.SmallSizes
import InitECandidate.Solver.Input.CurrentRlp.HeaderWriteFrame
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.CallPrefixTrace

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real branch phase sums its actual16child results and stored value
size, obtaining a nonwrapping payload<=limit+537 and retaining all nonlocals.
The zero incoming branch payload is to be supplied by the real begin frame. -/
theorem branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (fits : limit+537<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source branchChoice=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ payload.toNat≤limit+537) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "i" (.const 0#64) 0#64 (.seq scanLoop afterScan) rfl (selected.symm.trans normal)
  let entered:=bind source "i" 0#64
  obtain ⟨current,scanRun,valueRun⟩:=Input.sequence_none entered inner scanLoop afterScan continued
  obtain ⟨⟨accumulated,partialCell,partialBound⟩,scanFrame⟩:=scan_normal entered current 0#64 installed (bind_lookup_same _ _ _)
    ((bind_lookup_other source "i" "payload" 0#64 (by decide)).trans payloadCell) (by decide) scanRun
  have memory:=Input.LocalEffects.memory_of_erase entered current scanFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs scanFrame
  have codes:=Input.LocalEffects.code_of_erase entered current scanFrame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  have saved:=(Input.LocalPrefix.loop scanTest scan_body_safe).summary_full entered
  unfold Input.LocalSummary at saved
  rw [←scan_shapes.1,scanRun] at saved
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=
    (saved.1 rfl).trans ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell)
  have currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 160#64 168#64 limit domain (congrFun memory _) (congrFun memory _)
  rw [after_scan_shape] at valueRun
  obtain ⟨funded,values,body,callee,shape,built,returned,assigned,args,called,run,checked,assignRun,valueEnd⟩:=Input.CallNormal.scoped_none_data current inner "vl2" .one (ofString "rlp_value_encoded_len") valueArguments addValue valueRun
  let ready:=Input.CallNormal.continuationEntry current built "vl2" returned
  have reached : Input.CallPrefix.Reaches current (.scoped (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments) ready:=
    .scoped current _ _ _ _ values body callee shape returned built args called (by omega) run checked
  obtain ⟨encoded,_lower,upper,number,lengthCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal (ofString "vl2") valueArguments currentView.pointer currentView.length
    (by have size:=currentView.payload.1; omega) currentInstalled (value_arguments current node limit property currentView currentNode) reached
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word accumulated)):=
    (kept (ofString "payload") (by decide)).trans partialCell
  have read : eval ready (.op .add [localVar "payload",localVar "vl2"])=some (.val (.word (accumulated+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assignedEq:=Input.assign_none ready assigned "payload" (.op .add [localVar "payload",localVar "vl2"]) (accumulated+BitVec.ofNat 64 encoded) read assignRun
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,valueEnd,assignedEq]; rfl
  have payloadNumber : (accumulated+BitVec.ofNat 64 encoded).toNat=accumulated.toNat+encoded:=by
    rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; change accumulated.toNat≤528 at partialBound; omega),number]
  refine ⟨⟨accumulated+BitVec.ofNat 64 encoded,?_,?_⟩,finalFrame.trans (valueFrame.trans scanFrame)⟩
  · rw [endpoint,valueEnd,restore_lookup_other source (restore current "vl2" assigned) "i" "payload" (by decide),restore_lookup_other current assigned "vl2" "payload" (by decide),assignedEq]
    exact bind_lookup_same _ _ _
  · rw [payloadNumber]
    have size:=currentView.payload.1
    change accumulated.toNat≤528 at partialBound
    omega

/-- The real branch preparation returns precisely its sixteen child
references plus its exact encoded value size, retaining the incoming memory. -/
theorem branch_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (data : ReferenceScanData source node) (first : BitVec 64)
    (firstRead : view.length=1#64→eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (fits : limit+537<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source branchChoice=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length ∧ payload.toNat≤limit+537) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "i" (.const 0#64) 0#64 (.seq scanLoop afterScan) rfl (selected.symm.trans normal)
  let entered:=bind source "i" 0#64
  obtain ⟨current,scanRun,valueRun⟩:=Input.sequence_none entered inner scanLoop afterScan continued
  obtain ⟨⟨accumulated,partialCell,partialExact⟩,_finalIndex,scanFrame⟩:=scan_normal_exact entered current node 0#64 (data.of_frame rfl) installed
    ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell) (bind_lookup_same _ _ _)
    ((bind_lookup_other source "i" "payload" 0#64 (by decide)).trans payloadCell) (by decide) scanRun
  change accumulated.toNat=0+data.total 16 at partialExact
  have totalBound:=data.total_bound 16
  have partialBound : accumulated.toNat≤528:=by omega
  have memory:=Input.LocalEffects.memory_of_erase entered current scanFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs scanFrame
  have codes:=Input.LocalEffects.code_of_erase entered current scanFrame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  have saved:=(Input.LocalPrefix.loop scanTest scan_body_safe).summary_full entered
  unfold Input.LocalSummary at saved
  rw [←scan_shapes.1,scanRun] at saved
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=
    (saved.1 rfl).trans ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell)
  let currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 160#64 168#64 limit domain (congrFun memory _) (congrFun memory _)
  have currentFirst : currentView.length=1#64→eval current (.loadByte (.const currentView.pointer))=some (.val (.word first)):=by
    intro one
    change eval current (.loadByte (.const view.pointer))=some (.val (.word first))
    have byte:=firstRead one
    have endian:=congrArg PanSemStateFiniteExact.be scanFrame
    change current.be=source.be at endian
    have currentMemory : current.memory=source.memory:=memory
    have currentDomain : current.memaddrs=source.memaddrs:=domain
    simp only [eval,evalHOLExact,toExact,currentMemory,currentDomain,endian] at byte ⊢
    convert byte using 1 <;> congr 2 <;> apply Subsingleton.elim
  rw [after_scan_shape] at valueRun
  obtain ⟨funded,values,body,callee,shape,built,returned,assigned,args,called,run,checked,assignRun,valueEnd⟩:=Input.CallNormal.scoped_none_data current inner "vl2" .one (ofString "rlp_value_encoded_len") valueArguments addValue valueRun
  let ready:=Input.CallNormal.continuationEntry current built "vl2" returned
  have reached : Input.CallPrefix.Reaches current (.scoped (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments) ready:=
    .scoped current _ _ _ _ values body callee shape returned built args called (by omega) run checked
  obtain ⟨encoded,exactEncoded,_lower,upper,number,lengthCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal_exact (ofString "vl2") valueArguments currentView.pointer currentView.length first
    (by have size:=currentView.payload.1; omega) currentInstalled (value_arguments current node limit property currentView currentNode) currentFirst reached
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word accumulated)):=
    (kept (ofString "payload") (by decide)).trans partialCell
  have read : eval ready (.op .add [localVar "payload",localVar "vl2"])=some (.val (.word (accumulated+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assignedEq:=Input.assign_none ready assigned "payload" (.op .add [localVar "payload",localVar "vl2"]) (accumulated+BitVec.ofNat 64 encoded) read assignRun
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,valueEnd,assignedEq]; rfl
  have payloadNumber : (accumulated+BitVec.ofNat 64 encoded).toNat=accumulated.toNat+encoded:=by
    rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; omega),number]
  refine ⟨⟨accumulated+BitVec.ofNat 64 encoded,?_,?_,?_⟩,finalFrame.trans (valueFrame.trans scanFrame)⟩
  · rw [endpoint,valueEnd,restore_lookup_other source (restore current "vl2" assigned) "i" "payload" (by decide),restore_lookup_other current assigned "vl2" "payload" (by decide),assignedEq]
    exact bind_lookup_same _ _ _
  · rw [payloadNumber,partialExact,exactEncoded]
    simp only [currentView,TrieWalk.ValueView.of_agreement,Nat.zero_add]
  · rw [payloadNumber]
    have size:=currentView.payload.1
    omega

/-- The real finish buffer prefix has completed: its exact allocation is
funded by the observed normal allocator, and only its list header was written. -/
structure BufferOutput (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload : BitVec 64) (header : Nat) : Prop where
  headerExact : header=Input.RlpLength.Header.encodedLength payload
  headerLower : 1≤header
  headerUpper : header≤9
  room : heap.toNat+header+payload.toNat≤2952790016
  arena : AllocatedBytes.Arena heap (header+payload.toNat)
  headerCell : current.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 header)))
  bufferCell : current.locals.lookup (ofString "buf")=some (.val (.word heap))
  offsetCell : current.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 header)))
  locals : ∀ other : MlS,ofString "hl"≠other → ofString "buf"≠other → ofString "off"≠other → current.locals.lookup other=source.locals.lookup other
  fields : Input.MemoryMetadata.erase current=Input.MemoryMetadata.erase (PersistentAlloc.post source heap (BitVec.ofNat 64 (header+payload.toNat)))
  memory : ∀ query,CopyGeneral.Away heap query header→current.memory query=source.memory query
  heapCell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (header+payload.toNat)))))
  growth : heap.toNat+header+payload.toNat≤(PersistentAlloc.rounded heap (BitVec.ofNat 64 (header+payload.toNat))).toNat
  heapUpper : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (header+payload.toNat))).toNat≤2952790016
  heapAligned : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (header+payload.toNat))).toNat%8=0
  price : source.clock-current.clock≤32

/-- Connect the actual length/alloc/header/off actions to the true writer
entry. Neither allocation room nor later successful stores are inputs. -/
theorem buffer_normal (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (fits : payload.toNat+9<2^64)
    (trace : Input.CallPrefix.Execution source bufferTrace current) :
    ∃ header,BufferOutput source current heap payload header := by
  unfold bufferTrace at trace
  obtain ⟨sized,sizeReached,rest⟩:=trace.head
  have sizeArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "payload"]=some [.val (.word payload)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadCell]
  obtain ⟨header,headerExact,headerLower,headerUpper,firstHeader,kept,sizeFrame,sizePrice⟩:=Input.CurrentRlp.SmallSizes.scoped_list_header_normal_exact
    (ofString "hl") [localVar "payload"] payload installed sizeArgs sizeReached
  have sizedPayload : sized.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (kept (ofString "payload") (by decide)).trans payloadCell
  have sizedHeap : sized.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) sizeFrame
    exact same.trans heapCell
  have sizedInstalled : Input.OriginalCode.Installed sized.code:=by rw [Input.LocalEffects.code_of_erase source sized sizeFrame]; exact installed
  let amount:=BitVec.ofNat 64 (header+payload.toNat)
  have amountNumber : amount.toNat=header+payload.toNat:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite sized (h:=fun query=>Classical.propDecidable (sized.memaddrs query)) allocationArguments=some (PersistentAlloc.values amount):=by
    simp [allocationArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,firstHeader,sizedPayload,
      valueIsWord,valueWord,wordOpHOL,wordOp,PersistentAlloc.values,amount,BitVec.ofNat_add]
  obtain ⟨allocated,allocationReached,rest⟩:=rest.head
  obtain ⟨rawRoom,allocationEnd⟩:=allocationReached.alloc_target (ofString "buf") allocationArguments heap amount sizedInstalled args sizedHeap heapUpper
  have room : heap.toNat+header+payload.toNat≤2952790016:=by rw [amountNumber] at rawRoom; omega
  have allocationFrame : Input.LocalEffects.erase allocated=Input.LocalEffects.erase (PersistentAlloc.post source heap amount):=by
    rw [allocationEnd]
    exact congrArg (fun state=>PersistentAlloc.post state heap amount) sizeFrame
  have allocatedInstalled : Input.OriginalCode.Installed allocated.code:=by
    have code:=Input.LocalEffects.code_of_erase (PersistentAlloc.post source heap amount) allocated allocationFrame
    rw [code]; exact installed
  have allocBuffer : allocated.locals.lookup (ofString "buf")=some (.val (.word heap)):=by
    rw [allocationEnd]; simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have allocOther (other : MlS) (different : ofString "buf"≠other) : allocated.locals.lookup other=sized.locals.lookup other:=by
    rw [allocationEnd]; simp [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,different]
  have allocatedPayload : allocated.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (allocOther (ofString "payload") (by decide)).trans sizedPayload
  have headerArgs : evalListHOLFinite allocated (h:=fun query=>Classical.propDecidable (allocated.memaddrs query)) headerArguments=
      some [.val (.word heap),.val (.word payload)]:=by
    simp [headerArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,allocBuffer,allocatedPayload]
  obtain ⟨written,writeReached,rest⟩:=rest.head
  have headerRun : evaluateHOLFiniteState allocated (.call (some (none,none)) (ofString "rlp_encode_list_header") headerArguments)=(none,written):=by
    cases writeReached with
    | command _ _ run=>exact run
  have headerFrame:=Input.CurrentRlp.ListWrite.call_frame_exact allocated written headerArguments heap payload allocatedInstalled headerArgs headerRun
  rw [←headerExact] at headerFrame
  have writtenLocal (key : MlS) : written.locals.lookup key=allocated.locals.lookup key:=
    Input.CallNormal.ignored_lookup allocated written key (ofString "rlp_encode_list_header") headerArguments headerRun
  have writtenHeader : written.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 header))):=
    (writtenLocal (ofString "hl")).trans ((allocOther (ofString "hl") (by decide)).trans firstHeader)
  obtain ⟨ready,offsetReached,last⟩:=rest.head
  have currentEq : current=ready:=by cases last; rfl
  subst current
  have offsetRead : eval written (localVar "hl")=some (.val (.word (BitVec.ofNat 64 header))):=by
    simp [eval,evalHOLExact,toExact,localVar,writtenHeader]
  have offsetEnd:=offsetReached.declare_target (.val (.word (BitVec.ofNat 64 header))) offsetRead
  have finalOther (other : MlS) (different : ofString "off"≠other) : ready.locals.lookup other=written.locals.lookup other:=by
    rw [offsetEnd]; simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have finalFields : Input.MemoryMetadata.erase ready=Input.MemoryMetadata.erase (PersistentAlloc.post source heap amount):=by
    have pure : Input.MemoryMetadata.erase ready=Input.MemoryMetadata.erase written:=by rw [offsetEnd]; rfl
    exact pure.trans (headerFrame.metadata.trans (Input.MemoryMetadata.of_frame allocationFrame))
  have allocationMemory : allocated.memory=source.memory:=Input.LocalEffects.memory_of_erase (PersistentAlloc.post source heap amount) allocated allocationFrame
  have guards:=PersistentAlloc.guards heap amount rawRoom
  have writePrice:=Input.CurrentRlp.ListWrite.call_cost allocated headerArguments heap payload allocatedInstalled headerArgs
  rw [headerRun] at writePrice
  refine ⟨header,headerExact,headerLower,headerUpper,room,⟨heapLower,by omega⟩,?_,?_,?_,?_,finalFields,?_,?_,?_,guards.2.2.2.1,guards.2.2.2.2,?_⟩
  · exact (finalOther (ofString "hl") (by decide)).trans writtenHeader
  · exact (finalOther (ofString "buf") (by decide)).trans ((writtenLocal (ofString "buf")).trans allocBuffer)
  · rw [offsetEnd]; simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro other notHeader notBuffer notOffset
    exact (finalOther other notOffset).trans ((writtenLocal other).trans ((allocOther other notBuffer).trans (kept other notHeader)))
  · intro query away
    rw [offsetEnd]
    exact (headerFrame.memory query away).trans (congrFun allocationMemory query)
  · have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) finalFields
    simpa [Input.MemoryMetadata.erase,PersistentAlloc.post,emptyLocalsHOLFinite,HolFiniteMapExact.update,FUPDATE] using same
  · have grows:=guards.2.2.1
    change heap.toNat+amount.toNat≤(PersistentAlloc.rounded heap amount).toNat at grows
    change heap.toNat+header+payload.toNat≤(PersistentAlloc.rounded heap amount).toNat
    rw [amountNumber] at grows
    omega
  · have allocatedClock : allocated.clock=sized.clock-1:=by rw [allocationEnd]; rfl
    have funded:=allocationReached.scoped_funded
    rw [offsetEnd]
    change source.clock-written.clock≤32
    change allocated.clock-written.clock≤20 at writePrice
    omega

theorem BufferOutput.payload {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header)
    (cell : source.locals.lookup (ofString "payload")=some (.val (.word payload))) :
    current.locals.lookup (ofString "payload")=some (.val (.word payload)) :=
  (output.locals (ofString "payload") (by decide) (by decide) (by decide)).trans cell

theorem BufferOutput.runtime {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) :
    current.memaddrs=source.memaddrs ∧ current.be=source.be ∧ current.code=source.code := by
  have domain:=Input.MemoryMetadata.domain output.fields
  have endian:=Input.MemoryMetadata.endian output.fields
  have code:=Input.MemoryMetadata.code output.fields
  change current.memaddrs=source.memaddrs at domain
  change current.be=source.be at endian
  change current.code=source.code at code
  exact ⟨domain,endian,code⟩

theorem BufferOutput.before {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) (aligned : heap.toNat%8=0)
    (query : BitVec 64) (earlier : query.toNat<heap.toNat) : current.memory query=source.memory query := by
  have room:=output.room
  exact output.memory query (CopyGeneral.Away.after_floor heap query header heap.toNat aligned (Nat.le_refl _) (by omega) earlier)

theorem BufferOutput.above_cap {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) (query : BitVec 64) (above : 2952790016≤query.toNat) :
    current.memory query=source.memory query := by
  have room:=output.room
  exact output.memory query (CopyGeneral.Away.before heap query header 2952790016 (by omega) (by decide) above)

/-- Price the actual allocation/header/off remainder at its real scalar
bindings. Failed allocation or header writes remain covered outcomes. -/
theorem buffer_after_size_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload header : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (headerCell : source.locals.lookup (ofString "hl")=some (.val (.word header)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016) :
    source.clock-(evaluateHOLFiniteState source (Input.CallPrefix.program bufferTrace.tail .skip)).2.clock≤22 := by
  let amount:=header+payload
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values amount):=by
    simp [allocationArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,headerCell,payloadCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,PersistentAlloc.values,amount]
  let tailProgram : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") headerArguments) (.dec (ofString "off") .one (localVar "hl") .skip)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "buf") .one (ofString "alloc") allocationArguments tailProgram)).2.clock≤22
  apply Input.ClockCost.scoped_reached_current source "buf" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body tailProgram callee .one 1 20 args called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)
  intro built returned run _checked
  obtain ⟨answer,_room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) built heap amount amountCell heapCell heapUpper
    (Input.Trap.original_code source.code installed) returned run
  let ready:=Input.CallNormal.continuationEntry source built "buf" returned
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (Input.CallNormal.continuation_lookup_other source built "buf" "payload" returned (by decide)).trans payloadCell
  have readyBuffer : ready.locals.lookup (ofString "buf")=some (.val (.word heap)):=
    (Input.CallNormal.continuation_lookup_same source built "buf" returned).trans (congrArg some answer)
  have code:=congrArg PanSemStateFiniteExact.code frame
  change built.code=source.code at code
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed built.code; rw [code]; exact installed
  have headerArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) headerArguments=some [.val (.word heap),.val (.word payload)]:=by
    simp [headerArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,readyBuffer,readyPayload]
  have price:=Input.CurrentRlp.ListWrite.call_cost ready headerArguments heap payload readyInstalled headerArgs
  have rest : Input.ClockCost.Bound ready.code (.dec (ofString "off") .one (localVar "hl") .skip) 0:=
    Input.ClockCost.declared ready.code _ _ _ _ 0 (Input.ClockCost.skip ready.code)
  change ready.clock-(evaluateHOLFiniteState ready tailProgram).2.clock≤20
  exact Input.ClockCost.sequence_current ready _ _ 20 0 price rest

/-- All length/allocation/header/off outcomes consume at most33 source
call/loop ticks, before the writer continuation is allowed to run. -/
theorem buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016) :
    source.clock-(evaluateHOLFiniteState source (Input.CallPrefix.program bufferTrace .skip)).2.clock≤33 := by
  obtain ⟨callee,called,pCell⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "rlp_list_header_len") "payload_len"
    (Input.CurrentRlp.SmallSizes.body .listHeader) payload (Input.CurrentRlp.SmallSizes.list_header_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "payload"]=some [.val (.word payload)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadCell]
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"]
    (Input.CallPrefix.program bufferTrace.tail .skip))).2.clock≤33
  apply Input.ClockCost.scoped_reached_current source "hl" .one (ofString "rlp_list_header_len") [localVar "payload"] _
    (Input.CurrentRlp.SmallSizes.body .listHeader) (Input.CallPrefix.program bufferTrace.tail .skip) callee .one 10 22 args called
    (Input.CurrentRlp.SmallSizes.body_cost .listHeader (callEntryStateHOLFinite source callee) payload installed pCell)
  intro built returned run _checked
  obtain ⟨header,_exactHeader,_lower,_upper,answer,_price,frame⟩:=Input.CurrentRlp.SmallSizes.list_header_normal_exact
    (callEntryStateHOLFinite source callee) built payload installed pCell returned run
  let ready:=Input.CallNormal.continuationEntry source built "hl" returned
  have pure : Input.LocalEffects.erase ready=Input.LocalEffects.erase source:=frame
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [Input.LocalEffects.code_of_erase source ready pure]; exact installed
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (Input.CallNormal.continuation_lookup_other source built "hl" "payload" returned (by decide)).trans payloadCell
  have readyHeader : ready.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 header))):=
    (Input.CallNormal.continuation_lookup_same source built "hl" returned).trans (congrArg some answer)
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) pure).trans heapCell
  exact buffer_after_size_cost ready heap payload (BitVec.ofNat 64 header) readyInstalled readyPayload readyHeader readyHeap heapUpper

/-- The unchanged finish allocation scope either stops within the prefix
allowance or exposes its actual prepared writer entry and enclosing scope. -/
theorem buffer_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (fits : payload.toNat+9<2^64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source allocationScope=(outcome,post)) :
    source.clock-post.clock≤33 ∨ ∃ current inner header,Input.CallPrefix.Execution source bufferTrace current ∧ BufferOutput source current heap payload header ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤33 ∧ Input.CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current writerTail=(outcome,inner) := by
  rw [buffer_shape.1] at run
  rcases Input.CallPrefix.priced_frame_trace source post bufferTrace writerTail 33 (buffer_cost source heap payload installed payloadCell heapCell heapUpper) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,trace,forward,price,scope,continued⟩:=reached
    obtain ⟨header,output⟩:=buffer_normal source current heap payload installed payloadCell heapCell heapLower heapUpper fits trace
    exact Or.inr ⟨current,inner,header,trace,output,forward,price,scope,continued⟩

theorem branch_safe (key : MlS) (notIndex : key≠ofString "i") (notRef : key≠ofString "rl2")
    (notValue : key≠ofString "vl2") (notPayload : key≠ofString "payload") : Input.LocalPrefix key branchChoice := by
  have scanSafe : Input.LocalPrefix key scanBody:=by
    rw [scan_shapes.2.1]
    exact .decCall _ _ _ _ notRef (.seq (.assign _ _ notPayload) (.assign _ _ notIndex))
  have afterSafe : Input.LocalPrefix key afterScan:=by
    rw [after_scan_shape]
    exact .decCall _ _ _ _ notValue (.assign _ _ notPayload)
  rw [scan_shapes.2.2]
  exact .ite _ (.dec _ _ _ notIndex (.seq (by rw [scan_shapes.1]; exact .loop _ scanSafe) afterSafe)) .skip

/-- The complete actual branch preparation and buffer prefix is priced
before entering the writer:60 source ticks plus33 for the physical buffer. -/
theorem branch_buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (fits : limit+537<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016) :
    source.clock-(evaluateHOLFiniteState source (Input.CallPrefix.program (.command branchChoice::bufferTrace) .skip)).2.clock≤93 := by
  change source.clock-(evaluateHOLFiniteState source (.seq branchChoice (Input.CallPrefix.program bufferTrace .skip))).2.clock≤93
  apply Input.ClockCost.sequence_reached_current source branchChoice (Input.CallPrefix.program bufferTrace .skip) 60 33
    (branch_cost source node limit property view (by omega) installed nodeCell tagCell)
  intro prepared normal
  obtain ⟨⟨payload,cell,_bound⟩,frame⟩:=branch_normal source prepared node limit property view fits installed nodeCell tagCell payloadCell normal
  have nextInstalled : Input.OriginalCode.Installed prepared.code:=by rw [Input.LocalEffects.code_of_erase source prepared frame]; exact installed
  have nextHeap : prepared.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame).trans heapCell
  exact buffer_cost prepared heap payload nextInstalled cell nextHeap heapUpper

/-- Connect actual branch preparation to its real allocated writer entry,
retaining the original byte-count data and actual node/tag bindings. -/
theorem branch_buffer_normal (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (data : ReferenceScanData source node) (first : BitVec 64)
    (firstRead : view.length=1#64→eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (fits : limit+546<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (trace : Input.CallPrefix.Execution source (.command branchChoice::bufferTrace) current) :
    ∃ prepared payload header,Input.LocalEffects.erase prepared=Input.LocalEffects.erase source ∧
      payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length ∧ payload.toNat≤limit+537 ∧
      BufferOutput prepared current heap payload header ∧ current.locals.lookup (ofString "node")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 3#64)) := by
  obtain ⟨prepared,reached,rest⟩:=trace.head
  have normal : evaluateHOLFiniteState source branchChoice=(none,prepared):=by cases reached with | command _ _ run=>exact run
  obtain ⟨⟨payload,cell,exactCount,bound⟩,frame⟩:=branch_normal_exact source prepared node limit property view data first firstRead (by omega)
    installed nodeCell tagCell payloadCell normal
  have nextInstalled : Input.OriginalCode.Installed prepared.code:=by rw [Input.LocalEffects.code_of_erase source prepared frame]; exact installed
  have nextHeap : prepared.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame).trans heapCell
  obtain ⟨header,output⟩:=buffer_normal prepared current heap payload nextInstalled cell nextHeap heapLower heapUpper (by omega) rest
  have savedNode:=(branch_safe (ofString "node") (by decide) (by decide) (by decide) (by decide)).summary_full source
  have savedTag:=(branch_safe (ofString "k") (by decide) (by decide) (by decide) (by decide)).summary_full source
  unfold Input.LocalSummary at savedNode savedTag
  rw [normal] at savedNode savedTag
  exact ⟨prepared,payload,header,frame,exactCount,bound,output,
    (output.locals (ofString "node") (by decide) (by decide) (by decide)).trans ((savedNode.1 rfl).trans nodeCell),
    (output.locals (ofString "k") (by decide) (by decide) (by decide)).trans ((savedTag.1 rfl).trans tagCell)⟩

/-- The actual branch finish suffix stops within93 source ticks or reaches
its physical writer with the exact payload and allocated buffer retained. -/
theorem branch_buffer_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (data : ReferenceScanData source node) (first : BitVec 64)
    (firstRead : view.length=1#64→eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (fits : limit+546<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterExtension=(outcome,post)) :
    source.clock-post.clock≤93 ∨ ∃ current inner prepared payload header,
      Input.CallPrefix.Execution source (.command branchChoice::bufferTrace) current ∧ Input.LocalEffects.erase prepared=Input.LocalEffects.erase source ∧
      payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length ∧ payload.toNat≤limit+537 ∧
      BufferOutput prepared current heap payload header ∧ current.locals.lookup (ofString "node")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 3#64)) ∧ current.clock≤source.clock ∧ source.clock-current.clock≤93 ∧
      Input.CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current writerTail=(outcome,inner) := by
  have shape : afterExtension=Input.CallPrefix.program (.command branchChoice::bufferTrace) writerTail:=by rw [buffer_shape.2,buffer_shape.1]; rfl
  rw [shape] at run
  rcases Input.CallPrefix.priced_frame_trace source post (.command branchChoice::bufferTrace) writerTail 93
    (branch_buffer_cost source node heap limit property view (by omega) installed nodeCell tagCell payloadCell heapCell heapUpper) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,trace,forward,price,scope,continued⟩:=reached
    obtain ⟨prepared,payload,header,frame,exactCount,bound,output,nodeAfter,tagAfter⟩:=branch_buffer_normal source current node heap limit property view data first firstRead
      fits installed nodeCell tagCell payloadCell heapCell heapLower heapUpper trace
    exact Or.inr ⟨current,inner,prepared,payload,header,trace,frame,exactCount,bound,output,nodeAfter,tagAfter,forward,price,scope,continued⟩

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_normal_exact

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.payload
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.runtime
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.before
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.above_cap

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_after_size_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_trace

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_buffer_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_buffer_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_buffer_trace

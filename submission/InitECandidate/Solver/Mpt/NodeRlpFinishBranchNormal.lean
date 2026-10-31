import InitECandidate.Solver.Mpt.NodeRlpFinishBranchCost
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.CurrentRlp.SmallSizes
import InitECandidate.Solver.Input.CurrentRlp.HeaderWriteFrame
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostCurrentLoop
import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Input.CallPrefixLocals
import InitECandidate.Solver.Mpt.NodeWriteRef
import InitECandidate.Solver.Rlp.ValidationArena

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

theorem ReferenceScanData.writer_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (buffer offset index : BitVec 64) (active : index.toNat<16)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (indexCell : source.locals.lookup (ofString "j")=some (.val (.word index))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) writeChildArguments=
      some [.val (.word (data.child index.toNat)),.val (.word (buffer+offset))] := by
  obtain ⟨mapped,stored⟩:=data.slot index.toNat active
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] at mapped stored
  simp [writeChildArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,bufferCell,offsetCell,indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem ReferenceScanData.writer_bytes {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (i : Nat) :
    NodeWriteRef.referenceBytes (data.child i) (data.tag i) (data.length i).toNat=(data.word i).toNat := by
  have same:=NodeWriteRef.reference_word_eq (data.child i) (data.tag i) (data.length i).toNat (data.length i).isLt
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at same
  have bound:=NodeWriteRef.reference_bytes_bound (data.child i) (data.tag i) (data.length i).toNat
  have number : (BitVec.ofNat 64 (NodeWriteRef.referenceBytes (data.child i) (data.tag i) (data.length i).toNat)).toNat=
      NodeWriteRef.referenceBytes (data.child i) (data.tag i) (data.length i).toNat:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have native:=congrArg BitVec.toNat same
  rw [number] at native
  exact native.symm

theorem ReferenceScanData.hash_data {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (i : Nat) (inside : i<16) (heap : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (small : (data.length i).toNat+136<2^64) (active : data.child i≠0#64) (nonHash : data.tag i≠0#64) (populated : data.cached i≠0#64) :
    NodeHashCached.Data source (data.child i) heap (data.cached i) (data.length i).toNat := by
  obtain ⟨pointerMapped,pointerStored⟩:=data.cache i inside active nonHash
  obtain ⟨lengthMapped,lengthStored⟩:=data.size i inside active nonHash populated
  exact ⟨installed,pointerMapped,pointerStored,lengthMapped,by simpa using lengthStored,heapCell,heapUpper,small⟩

theorem write_body_safe (key : MlS) (notResult : key≠ofString "w4") (notOffset : key≠ofString "off") (notIndex : key≠ofString "j") :
    Input.LocalPrefix key writeBody := by
  rw [write_shapes.2.2.2.2]
  exact .decCall _ _ _ _ notResult (.seq (.assign _ _ notOffset) (.assign _ _ notIndex))

theorem write_body_advance : Input.CounterFlow.Advances (ofString "j") 1 writeBody := by
  rw [write_shapes.2.2.2.2]
  apply Input.CounterFlow.scoped_call (ofString "j") "w4" .one _ _ _ 1 (by decide)
  exact Input.CounterFlow.sequence _ _ _ 0 1 (Input.CounterFlow.preserved _ addWritten (.assign _ _ (by decide))) (Input.CounterFlow.increment _)

/-- Every outcome of the real child-write iteration, including a failed
cache read/hash/copy, has its actual length-based source allowance. -/
theorem write_iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset index heap : BitVec 64)
    (data : ReferenceScanData source node) (active : index.toNat<16)
    (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (indexCell : source.locals.lookup (ofString "j")=some (.val (.word index)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (small : (data.length index.toNat).toNat+136<2^64) :
    source.clock-(evaluateHOLFiniteState source writeBody).2.clock≤CurrentKeccak.Hash.bodyPrice (data.length index.toNat).toNat+47 := by
  obtain ⟨callee,called,childCell,_dstCell⟩:=NodeWriteRef.environment source.code.lookup (data.child index.toNat) (buffer+offset) (NodeWriteRef.original_code source.code installed)
  have price:=NodeWriteRef.body_cost (callEntryStateHOLFinite source callee) (data.child index.toNat) (data.tag index.toNat) heap (data.cached index.toNat) (data.length index.toNat).toNat
    installed childCell (data.header index.toNat active) (data.cache index.toNat active)
    (fun live nonHash populated=>(data.hash_data index.toNat active heap installed heapCell heapUpper small live nonHash populated).of_frame rfl)
  rw [write_shapes.2.2.2.2]
  have result:=Input.ClockCost.scoped_current source (ofString "w4") .one (ofString "node_write_ref") writeChildArguments _ NodeWriteRef.body (.seq addWritten writeAdvance)
    callee .one (CurrentKeccak.Hash.bodyPrice (data.length index.toNat).toNat+46) 0 (data.writer_arguments buffer offset index active nodeCell bufferCell offsetCell indexCell) called price
    (Input.ClockCost.sequence source.code _ _ 0 0 (Input.ClockCost.assign source.code _ _) (Input.ClockCost.assign source.code _ _))
  simpa only [Nat.add_zero,Nat.add_assoc] using result

/-- The actual scoped child writer supplies its true reference count and
whole heap/memory frame, followed by the real off/j assignments and restoration. -/
theorem write_iteration_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset index heap cached stp pad : BitVec 64)
    (data : ReferenceScanData source node) (active : index.toNat<16)
    (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (indexCell : source.locals.lookup (ofString "j")=some (.val (.word index)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (small : (data.length index.toNat).toNat+136<2^64)
    (digestMapped : data.child index.toNat≠0#64→data.tag index.toNat≠0#64→data.cached index.toNat≠0#64→source.memaddrs (data.child index.toNat+24#64))
    (digestStored : source.memory (data.child index.toNat+24#64)=.word cached)
    (normal : evaluateHOLFiniteState source writeBody=(none,post)) :
    ∃ output : NodeWriteRef.Output source post (data.child index.toNat) (buffer+offset) heap cached stp pad (.val (.word (BitVec.ofNat 64 (data.word index.toNat).toNat))),
      output.bytes=(data.word index.toNat).toNat ∧ (data.child index.toNat=0#64→ output.hashed=false) ∧ post.locals.lookup (ofString "j")=some (.val (.word (index+1#64))) ∧
      post.locals.lookup (ofString "off")=some (.val (.word (offset+data.word index.toNat))) := by
  have shaped:=normal
  rw [write_shapes.2.2.2.2] at shaped
  obtain ⟨funded,values,actualBody,callee,shape,childTarget,returned,inner,args,called,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none_data source post "w4" .one
    (ofString "node_write_ref") writeChildArguments (.seq addWritten writeAdvance) shaped
  let ready:=Input.CallNormal.continuationEntry source childTarget "w4" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "w4") .one (ofString "node_write_ref") writeChildArguments) ready:=
    .scoped source _ _ _ _ values actualBody callee shape returned childTarget args called (by omega) run checked
  have results:=NodeWriteRef.reached_normal_exact source ready "w4" writeChildArguments (data.child index.toNat) (buffer+offset) (data.tag index.toNat)
    heap (data.cached index.toNat) cached stp pad (data.length index.toNat).toNat environment heapLower
    (data.writer_arguments buffer offset index active nodeCell bufferCell offsetCell indexCell) (data.header index.toNat active) (data.cache index.toNat active)
    (fun live nonHash populated=>data.hash_data index.toNat active heap environment.installed heapCell heapUpper small live nonHash populated)
    (fun live nonHash populated=>⟨digestMapped live nonHash populated,digestStored⟩) reached
  rw [data.writer_bytes index.toNat] at results
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at results
  obtain ⟨lengthCell,output,size,noHash⟩:=results
  have readyOffset : ready.locals.lookup (ofString "off")=some (.val (.word offset)):=
    ((Input.CallPrefix.KeepsLocal.scoped (ofString "off") (ofString "w4") .one (ofString "node_write_ref") writeChildArguments (by decide)) source ready reached).trans offsetCell
  obtain ⟨afterAdd,addRun,advanceRun⟩:=Input.sequence_none ready inner addWritten writeAdvance continued
  have read : eval ready (.op .add [localVar "off",localVar "w4"])=some (.val (.word (offset+data.word index.toNat))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyOffset,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have afterAddEq:=Input.assign_none ready afterAdd "off" (.op .add [localVar "off",localVar "w4"]) (offset+data.word index.toNat) read addRun
  have keep:=(Input.LocalPrefix.assign (key:=ofString "off") (ofString "j") (.op .add [localVar "j",.const 1#64]) (by decide)).summary_full afterAdd
  change Input.LocalSummary (ofString "off") writeAdvance afterAdd at keep
  unfold Input.LocalSummary at keep
  rw [advanceRun] at keep
  have finalOffset : inner.locals.lookup (ofString "off")=some (.val (.word (offset+data.word index.toNat))):=by
    rw [keep.1 rfl,afterAddEq]
    exact bind_lookup_same _ _ _
  have frame:=Input.LocalEffects.sequence ready.code addWritten writeAdvance (Input.LocalEffects.assign ready.code _ _) (Input.LocalEffects.assign ready.code _ _) ready rfl
  rw [continued] at frame
  have finalFrame : Input.LocalEffects.erase post=Input.LocalEffects.erase ready:=by rw [endpoint]; exact frame
  let lifted:=output.reframe rfl finalFrame
  refine ⟨lifted,size,noHash,write_body_advance source post index indexCell normal,?_⟩
  rw [endpoint,restore_lookup_other source inner "w4" "off" (by decide)]
  exact finalOffset

/-- Incoming physical separation for queries retained by the child writer.
It refers only to existing node/input/workspace locations, never future success. -/
structure WriteProtection (children : Nat→BitVec 64) (buffer stp pad : BitVec 64) (keep : BitVec 64→Prop) : Prop where
  earlier : ∀ query,keep query→query.toNat<buffer.toNat
  stateAway : ∀ query,keep query→CopyGeneral.Away stp query 200
  padAway : ∀ query,keep query→CopyGeneral.Away pad query 136
  cacheAway : ∀ i,i<16→children i≠0#64→∀ query,keep query→query≠children i+24#64
  cacheBefore : ∀ i,i<16→(children i+24#64).toNat<2952790016
  stateBefore : stp.toNat+200≤2952790016
  padBefore : pad.toNat+136≤2952790016

/-- A real writer iteration preserves each separated incoming query.
Null children use their exact destination-only frame, including query24. -/
theorem write_iteration_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer offset heap cached stp pad : BitVec 64} {i : Nat}
    {data : ReferenceScanData source node} {value : ValueHOL 64} {keep : BitVec 64→Prop}
    (output : NodeWriteRef.Output source post (data.child i) (buffer+offset) heap cached stp pad value)
    (noHash : data.child i=0#64→ output.hashed=false)
    (protection : WriteProtection data.child buffer stp pad keep) (active : i<16)
    (aligned : buffer.toNat%8=0) (heapFloor : buffer.toNat≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (inside : buffer.toNat+offset.toNat+output.bytes≤2952790016)
    (query : BitVec 64) (required : keep query) : post.memory query=source.memory query := by
  have before:=protection.earlier query required
  have dstNumber : (buffer+offset).toNat=buffer.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by omega)
  have dstAway : CopyGeneral.Away (buffer+offset) query output.bytes:=
    CopyGeneral.Away.after_floor (buffer+offset) query output.bytes buffer.toNat aligned (by rw [dstNumber]; omega) (by rw [dstNumber]; omega) before
  by_cases null : data.child i=0#64
  · exact output.fastMemory (noHash null) query dstAway
  · exact output.memory query dstAway (protection.cacheAway i active null query required) (protection.stateAway query required) (protection.padAway query required)
      (fun _hashed _zero=>CopyGeneral.Away.after_floor heap query 32 buffer.toNat aligned heapFloor (by omega) before)

/-- Each actual normal write retains all stable reference inputs. Its
mutable hash-cache word is read anew by later calls, without a stale-value model. -/
def ReferenceScanData.after_write {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer offset heap cached stp pad : BitVec 64} {i : Nat}
    (data : ReferenceScanData source node) {value : ValueHOL 64} {keep : BitVec 64→Prop}
    (output : NodeWriteRef.Output source post (data.child i) (buffer+offset) heap cached stp pad value)
    (noHash : data.child i=0#64→ output.hashed=false)
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query→keep query)
    (active : i<16) (aligned : buffer.toNat%8=0) (heapFloor : buffer.toNat≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (inside : buffer.toNat+offset.toNat+output.bytes≤2952790016) : ReferenceScanData post node :=
  data.of_memory output.runtime.1 (fun query required=>write_iteration_memory output noHash protection active aligned heapFloor heapUpper inside query (covers query required))

theorem write_iteration_above_cap {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer offset heap cached stp pad : BitVec 64} {i : Nat}
    {data : ReferenceScanData source node} {value : ValueHOL 64} {keep : BitVec 64→Prop}
    (output : NodeWriteRef.Output source post (data.child i) (buffer+offset) heap cached stp pad value)
    (protection : WriteProtection data.child buffer stp pad keep) (active : i<16)
    (inside : buffer.toNat+offset.toNat+output.bytes≤2952790016)
    (query : BitVec 64) (above : 2952790016≤query.toNat) : post.memory query=source.memory query := by
  have dstNumber : (buffer+offset).toNat=buffer.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by omega)
  exact output.above_cap (by rw [dstNumber]; omega) (protection.cacheBefore i active) protection.stateBefore protection.padBefore query above

/-- The actual current loop state: exact offset, bounded hash heap and
retained source queries. A later callee return is not part of this model. -/
structure WriteModel (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer stp pad : BitVec 64)
    (data : ReferenceScanData origin node) (keep : BitVec 64 → Prop) (start span i : Nat) (heap : BitVec 64) : Prop where
  bounded : i≤16
  indexCell : current.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 i)))
  nodeCell : current.locals.lookup (ofString "node")=some (.val (.word node))
  bufferCell : current.locals.lookup (ofString "buf")=some (.val (.word buffer))
  offsetCell : current.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (start+data.total i))))
  heapCell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapUpper : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  heapFloor : buffer.toNat+span≤heap.toNat
  environment : CurrentKeccak.Hash.Environment current stp pad
  runtime : current.memaddrs=origin.memaddrs ∧ current.be=origin.be ∧ current.code=origin.code
  memory : ∀ query,keep query → current.memory query=origin.memory query
  scratch : ∀ query,2952790016≤query.toNat → current.memory query=origin.memory query
  metadata : Rlp.Validation.scratchMetadata current=Rlp.Validation.scratchMetadata origin
  globals : HeapGlobals origin current

/-- Construct the next complete model from this iteration's actual normal
execution. Shared children use the current HASH24 value on every call. -/
theorem write_model_step {origin current post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap)
    (active : i<16) (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat)
    (budget : start+data.total 16≤span) (protection : WriteProtection data.child buffer stp pad keep)
    (covers : ∀ query,data.Footprint query → keep query)
    (small : ∀ j,j<16 → (data.length j).toNat+136<2^64)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    (normal : evaluateHOLFiniteState current writeBody=(none,post)) :
    ∃ nextHeap,WriteModel origin post node buffer stp pad data keep start span (i+1) nextHeap := by
  let currentData : ReferenceScanData current node:=data.of_memory model.runtime.1 (fun query required=>model.memory query (covers query required))
  let index:=BitVec.ofNat 64 i
  let offset:=BitVec.ofNat 64 (start+data.total i)
  have indexNumber : index.toNat=i:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nextBudget : start+data.total i+(data.word i).toNat≤span:=by
    have prefixBound:=data.total_mono (i+1) 16 (by omega)
    change data.total i+(data.word i).toNat≤data.total 16 at prefixBound
    omega
  have offsetNumber : offset.toNat=start+data.total i:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have floor:=model.heapFloor; have cap:=model.heapUpper; omega)]
  obtain ⟨cached,cacheStored⟩ : ∃ cached : BitVec 64,current.memory (data.child i+24#64)=.word cached:=by
    cases stored : current.memory (data.child i+24#64) with
    | word word=>exact ⟨word,rfl⟩
  have infos:=write_iteration_normal current post node buffer offset index heap cached stp pad currentData
    (by rw [indexNumber]; exact active) model.environment (by have floor:=model.heapFloor; omega)
    model.nodeCell model.bufferCell model.offsetCell model.indexCell model.heapCell model.heapUpper (by rw [indexNumber]; exact small i active)
    (by
      intro live nonHash populated
      simp only [indexNumber] at live nonHash populated ⊢
      rw [model.runtime.1]
      exact digestMapped i active live nonHash populated)
    (by rw [indexNumber]; change current.memory (data.child i+24#64)=.word cached; exact cacheStored) normal
  rw [indexNumber] at infos
  obtain ⟨output,size,noHash,indexAfter,offsetAfter⟩:=infos
  have actualSize : output.bytes=(data.word i).toNat:=size
  have inside : buffer.toNat+offset.toNat+output.bytes≤2952790016:=by
    rw [offsetNumber,actualSize]
    have floor:=model.heapFloor
    have cap:=model.heapUpper
    omega
  have savedNode:=(write_body_safe (ofString "node") (by decide) (by decide) (by decide)).summary_full current
  have savedBuffer:=(write_body_safe (ofString "buf") (by decide) (by decide) (by decide)).summary_full current
  unfold Input.LocalSummary at savedNode savedBuffer
  rw [normal] at savedNode savedBuffer
  obtain ⟨nextCell,grows,bounded,nextAligned⟩:=output.heap model.heapCell model.heapUpper model.heapAligned
  have nextOffset : offset+currentData.word i=BitVec.ofNat 64 (start+data.total (i+1)):=by
    change BitVec.ofNat 64 (start+data.total i)+data.word i=BitVec.ofNat 64 (start+data.total (i+1))
    simp only [ReferenceScanData.total,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc,Nat.add_assoc]
  refine ⟨NodeWriteRef.outputHeap heap cached output.hashed,by
    refine ⟨by omega,?_,(savedNode.1 rfl).trans model.nodeCell,(savedBuffer.1 rfl).trans model.bufferCell,?_,nextCell,bounded,nextAligned,
      Nat.le_trans model.heapFloor grows,output.environment model.environment,?_,?_,?_,?_,model.globals.trans output.heap_globals⟩
    · simpa only [index,BitVec.ofNat_add] using indexAfter
    · rw [nextOffset] at offsetAfter
      exact offsetAfter
    · exact ⟨output.runtime.1.trans model.runtime.1,output.runtime.2.1.trans model.runtime.2.1,output.runtime.2.2.trans model.runtime.2.2⟩
    · intro query required
      exact (write_iteration_memory (source:=current) (post:=post) (data:=currentData) (offset:=offset) (i:=i) output noHash protection active aligned (by have floor:=model.heapFloor; omega) model.heapUpper inside query required).trans (model.memory query required)
    · intro query above
      exact (write_iteration_above_cap (source:=current) (post:=post) (data:=currentData) (offset:=offset) (i:=i) output protection active inside query above).trans (model.scratch query above)
    · have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) output.fields
      have base : Rlp.Validation.scratchMetadata (NodeWriteRef.outputBase current heap cached output.hashed)=Rlp.Validation.scratchMetadata current:=by
        unfold NodeWriteRef.outputBase
        split
        · unfold NodeHashCached.resultBase
          split <;> rfl
        · rfl
      have same : Rlp.Validation.scratchMetadata post=Rlp.Validation.scratchMetadata (NodeWriteRef.outputBase current heap cached output.hashed):=projected
      exact same.trans (base.trans model.metadata)⟩

theorem WriteModel.dec_clock {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap) :
    WriteModel origin (decClockHOLFinite current) node buffer stp pad data keep start span i heap :=
  {model with environment:=model.environment.of_frame rfl}

theorem write_model_cost {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap) (active : i<16) (limit : Nat)
    (lengths : ∀ j,j<16 → (data.length j).toNat≤limit) (small : limit+136<2^64)
    (covers : ∀ query,data.Footprint query → keep query) :
    current.clock-(evaluateHOLFiniteState current writeBody).2.clock≤CurrentKeccak.Hash.bodyPrice limit+47 := by
  let currentData : ReferenceScanData current node:=data.of_memory model.runtime.1 (fun query required=>model.memory query (covers query required))
  let index:=BitVec.ofNat 64 i
  let offset:=BitVec.ofNat 64 (start+data.total i)
  have indexNumber : index.toNat=i:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have bound:=lengths i active
  have price:=write_iteration_cost current node buffer offset index heap currentData (by rw [indexNumber]; exact active)
    model.environment.installed model.nodeCell model.bufferCell model.offsetCell model.indexCell model.heapCell model.heapUpper (by rw [indexNumber]; change (data.length i).toNat+136<2^64; omega)
  rw [indexNumber] at price
  change current.clock-(evaluateHOLFiniteState current writeBody).2.clock≤CurrentKeccak.Hash.bodyPrice (data.length i).toNat+47 at price
  have monotone : CurrentKeccak.Hash.bodyPrice (data.length i).toNat+47≤CurrentKeccak.Hash.bodyPrice limit+47:=by
    unfold CurrentKeccak.Hash.bodyPrice
    omega
  exact Nat.le_trans price monotone

def writeRank (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=16-(Input.CounterFlow.counterWord current (ofString "j")).toNat

theorem WriteModel.rank {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap) : writeRank current=16-i := by
  have number : (BitVec.ofNat 64 i).toNat=i:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=model.bounded; omega)]
  simp only [writeRank,Input.CounterFlow.counterWord,model.indexCell,Option.getD_some,valueWord,number]

theorem write_test_value (current : PanSemStateFiniteExact 64 Guest.HostMemory) (i : Nat) (bounded : i≤16)
    (cell : current.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 i)))) :
    evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word (if i<16 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 i).toNat=i:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have small : i<9223372036854775808:=by omega
  simp [writeTest,evalHOLFinite,evalHOLExact,toExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,small]

theorem write_test_active {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap) (word : BitVec 64)
    (observed : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)))
    (nonzero : word≠0#64) : i<16 := by
  have expected:=write_test_value current i model.bounded model.indexCell
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using observed.symm.trans expected
  exact nonzero zero

/-- All outcomes of the actual signed child-write loop have a finite
remaining-iteration allowance, using only its current physical model. -/
theorem write_loop_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span initial : Nat} {heap : BitVec 64}
    (model : WriteModel origin source node buffer stp pad data keep start span initial heap)
    (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat) (budget : start+data.total 16≤span)
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (limit : Nat) (lengths : ∀ j,j<16 → (data.length j).toNat≤limit) (small : limit+136<2^64)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64)) :
    source.clock-(evaluateHOLFiniteState source writeLoop).2.clock≤(CurrentKeccak.Hash.bodyPrice limit+48)*(16-initial) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ i heap,WriteModel origin current node buffer stp pad data keep start span i heap
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)) → word≠0#64 →
      0<writeRank current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) writeBody
        (output.1=none ∨ output.1=some .continue) → invariant output.2 ∧ writeRank output.2<writeRank current):=by
    intro current _code ⟨i,heap,ready⟩ word observed nonzero
    have active:=write_test_active ready word observed nonzero
    refine ⟨by rw [ready.rank]; omega,?_⟩
    intro _funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) writeBody
    have safe:=(write_body_safe (ofString "node") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at safe
    have isNormal : output.1=none:=continuing.resolve_right safe.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite current) writeBody=(none,output.2):=Prod.ext isNormal rfl
    obtain ⟨nextHeap,next⟩:=write_model_step ready.dec_clock active aligned bufferLower budget protection covers (by intro j inside; have bound:=lengths j inside; omega) digestMapped run
    exact ⟨⟨i+1,nextHeap,next⟩,by rw [next.rank,ready.rank]; omega⟩
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)) → word≠0#64 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) writeBody).2.clock≤CurrentKeccak.Hash.bodyPrice limit+47:=by
    intro current _code ⟨i,heap,ready⟩ word observed nonzero _funded
    exact write_model_cost ready.dec_clock (write_test_active ready word observed nonzero) limit lengths small covers
  have cost:=Input.ClockCost.ranked_loop_current source.code writeTest writeBody (CurrentKeccak.Hash.bodyPrice limit+47) invariant writeRank priced progress source rfl ⟨initial,heap,model⟩
  rw [model.rank] at cost
  rw [write_shapes.2.2.2.1]
  simpa only [Nat.add_assoc] using cost

/-- A genuine normal exit has written all sixteen exact reference counts,
retaining its bounded heap, source queries and complete high scratch frame. -/
theorem write_loop_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span initial : Nat} {heap : BitVec 64}
    (model : WriteModel origin source node buffer stp pad data keep start span initial heap)
    (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat) (budget : start+data.total 16≤span)
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (small : ∀ j,j<16 → (data.length j).toNat+136<2^64)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    (normal : evaluateHOLFiniteState source writeLoop=(none,post)) :
    ∃ nextHeap,WriteModel origin post node buffer stp pad data keep start span 16 nextHeap := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ i heap,WriteModel origin current node buffer stp pad data keep start span i heap
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)) → word≠0#64 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) writeBody=(none,target) → invariant target:=by
    intro current _code ⟨i,heap,ready⟩ word observed nonzero _funded target run
    obtain ⟨nextHeap,next⟩:=write_model_step ready.dec_clock (write_test_active ready word observed nonzero) aligned bufferLower budget protection covers small digestMapped run
    exact ⟨i+1,nextHeap,next⟩
  have shaped:=normal
  rw [write_shapes.2.2.2.1] at shaped
  obtain ⟨i,heap,ready⟩:=Input.loop_invariant source.code (ofString "node") writeTest writeBody
    (write_body_safe (ofString "node") (by decide) (by decide) (by decide)) invariant step source post rfl ⟨initial,heap,model⟩ shaped
  have noBreak : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState current writeBody).1≠some .break:=by
    intro current
    exact (write_body_safe (ofString "node") (by decide) (by decide) (by decide)).summary_full current |>.2.2.1
  have exit:=Input.loop_normal_exit writeTest writeBody noBreak source post shaped
  have expected:=write_test_value post i ready.bounded ready.indexCell
  have count : i=16:=by
    by_contra different
    have active : i<16:=by have bound:=ready.bounded; omega
    rw [exit,if_pos active] at expected
    cases expected
  exact ⟨heap,by simpa only [count] using ready⟩

theorem BufferOutput.globals {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) : HeapGlobals source current := by
  intro key different
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) output.fields
  change current.globals.lookup key=(PersistentAlloc.post source heap (BitVec.ofNat 64 (header+payload.toNat))).globals.lookup key at same
  exact same.trans (HeapGlobals.update source _ key different)

theorem BufferOutput.metadata {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) : Rlp.Validation.scratchMetadata current=Rlp.Validation.scratchMetadata source := by
  exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) output.fields

theorem BufferOutput.environment {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {heap payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) (environment : CurrentKeccak.Hash.Environment source stp pad) :
    CurrentKeccak.Hash.Environment current stp pad :=
  ⟨by rw [output.runtime.2.2]; exact environment.installed,output.runtime.1.trans environment.domain,
    (output.globals _ (by decide)).trans environment.stateGlobal,(output.globals _ (by decide)).trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

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

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.writer_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.writer_bytes
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.hash_data
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_body_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_body_advance
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_iteration_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_iteration_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_iteration_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_iteration_above_cap

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_model_step

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_model_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteModel.rank
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_test_value
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_test_active
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_loop_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_loop_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.globals
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.metadata
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.environment

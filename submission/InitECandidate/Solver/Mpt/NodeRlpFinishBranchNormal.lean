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
import InitECandidate.Solver.Mpt.TrieGraphCacheOffsets
import InitECandidate.Solver.Mpt.TrieGraphPathBytes

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
    (domain : source.memaddrs=InitE.ordinaryDomain) (active : data.child i≠0#64) (nonHash : data.tag i≠0#64) (populated : data.cached i≠0#64) :
    NodeHashCached.Data source (data.child i) heap (data.cached i) (data.length i).toNat := by
  obtain ⟨pointerMapped,pointerStored⟩:=data.cache i inside active nonHash
  obtain ⟨lengthMapped,lengthStored⟩:=data.size i inside active nonHash populated
  exact ⟨installed,pointerMapped,pointerStored,lengthMapped,by simpa using lengthStored,heapCell,heapUpper,(data.length i).isLt,domain⟩

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
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    source.clock-(evaluateHOLFiniteState source writeBody).2.clock≤CurrentKeccak.Hash.boundedBodyPrice (data.length index.toNat).toNat+47 := by
  obtain ⟨callee,called,childCell,_dstCell⟩:=NodeWriteRef.environment source.code.lookup (data.child index.toNat) (buffer+offset) (NodeWriteRef.original_code source.code installed)
  have price:=NodeWriteRef.body_bounded_cost (callEntryStateHOLFinite source callee) (data.child index.toNat) (data.tag index.toNat) heap (data.cached index.toNat) (data.length index.toNat).toNat
    installed childCell (data.header index.toNat active) (data.cache index.toNat active)
    (fun live nonHash populated=>(data.hash_data index.toNat active heap installed heapCell heapUpper domain live nonHash populated).of_frame rfl)
  rw [write_shapes.2.2.2.2]
  have result:=Input.ClockCost.scoped_current source (ofString "w4") .one (ofString "node_write_ref") writeChildArguments _ NodeWriteRef.body (.seq addWritten writeAdvance)
    callee .one (CurrentKeccak.Hash.boundedBodyPrice (data.length index.toNat).toNat+46) 0 (data.writer_arguments buffer offset index active nodeCell bufferCell offsetCell indexCell) called price
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
    (fun live nonHash populated=>data.hash_data index.toNat active heap environment.installed heapCell heapUpper environment.domain live nonHash populated)
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

/-- Original selected queries together with an existing persistent band. -/
def WithBand (keep : BitVec 64 → Prop) (lower upper : Nat) (query : BitVec 64) : Prop:=
  keep query ∨ (lower≤query.toNat ∧ query.toNat<upper)

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

/-- Actual child hash work lies before this older persistent band, while
all fresh output/digest writes lie at or beyond its upper frontier. -/
theorem WriteProtection.with_band {children : Nat → BitVec 64} {buffer stp pad : BitVec 64} {keep : BitVec 64 → Prop}
    (protection : WriteProtection children buffer stp pad keep) (lower : Nat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (cacheBefore : ∀ i,i<16 → children i≠0#64 → (children i+24#64).toNat<lower) :
    WriteProtection children buffer stp pad (WithBand keep lower buffer.toNat) := by
  refine ⟨?_,?_,?_,?_,protection.cacheBefore,protection.stateBefore,protection.padBefore⟩
  · intro query required
    rcases required with original|band
    · exact protection.earlier query original
    · exact band.2
  · intro query required
    rcases required with original|band
    · exact protection.stateAway query original
    · exact CopyGeneral.Away.before stp query 200 lower stateBefore (by have small:=query.isLt; omega) band.1
  · intro query required
    rcases required with original|band
    · exact protection.padAway query original
    · exact CopyGeneral.Away.before pad query 136 lower padBefore (by have small:=query.isLt; omega) band.1
  · intro i inside live query required
    rcases required with original|band
    · exact protection.cacheAway i inside live query original
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      have before:=cacheBefore i inside live
      omega

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
    model.nodeCell model.bufferCell model.offsetCell model.indexCell model.heapCell model.heapUpper
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
    (lengths : ∀ j,j<16 → (data.length j).toNat≤limit)
    (covers : ∀ query,data.Footprint query → keep query) :
    current.clock-(evaluateHOLFiniteState current writeBody).2.clock≤CurrentKeccak.Hash.boundedBodyPrice limit+47 := by
  let currentData : ReferenceScanData current node:=data.of_memory model.runtime.1 (fun query required=>model.memory query (covers query required))
  let index:=BitVec.ofNat 64 i
  let offset:=BitVec.ofNat 64 (start+data.total i)
  have indexNumber : index.toNat=i:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have bound:=lengths i active
  have price:=write_iteration_cost current node buffer offset index heap currentData (by rw [indexNumber]; exact active)
    model.environment.installed model.nodeCell model.bufferCell model.offsetCell model.indexCell model.heapCell model.heapUpper model.environment.domain
  rw [indexNumber] at price
  change current.clock-(evaluateHOLFiniteState current writeBody).2.clock≤CurrentKeccak.Hash.boundedBodyPrice (data.length i).toNat+47 at price
  have monotone : CurrentKeccak.Hash.boundedBodyPrice (data.length i).toNat+47≤CurrentKeccak.Hash.boundedBodyPrice limit+47:=by
    unfold CurrentKeccak.Hash.boundedBodyPrice CurrentKeccak.Hash.bodyPrice
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
    (limit : Nat) (lengths : ∀ j,j<16 → (data.length j).toNat≤limit)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64)) :
    source.clock-(evaluateHOLFiniteState source writeLoop).2.clock≤(CurrentKeccak.Hash.boundedBodyPrice limit+48)*(16-initial) := by
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
    obtain ⟨nextHeap,next⟩:=write_model_step ready.dec_clock active aligned bufferLower budget protection covers digestMapped run
    exact ⟨⟨i+1,nextHeap,next⟩,by rw [next.rank,ready.rank]; omega⟩
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)) → word≠0#64 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) writeBody).2.clock≤CurrentKeccak.Hash.boundedBodyPrice limit+47:=by
    intro current _code ⟨i,heap,ready⟩ word observed nonzero _funded
    exact write_model_cost ready.dec_clock (write_test_active ready word observed nonzero) limit lengths covers
  have cost:=Input.ClockCost.ranked_loop_current source.code writeTest writeBody (CurrentKeccak.Hash.boundedBodyPrice limit+47) invariant writeRank priced progress source rfl ⟨initial,heap,model⟩
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
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    (normal : evaluateHOLFiniteState source writeLoop=(none,post)) :
    ∃ nextHeap,WriteModel origin post node buffer stp pad data keep start span 16 nextHeap := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ i heap,WriteModel origin current node buffer stp pad data keep start span i heap
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) writeTest=some (.val (.word word)) → word≠0#64 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) writeBody=(none,target) → invariant target:=by
    intro current _code ⟨i,heap,ready⟩ word observed nonzero _funded target run
    obtain ⟨nextHeap,next⟩:=write_model_step ready.dec_clock (write_test_active ready word observed nonzero) aligned bufferLower budget protection covers digestMapped run
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


/-- The actual buffer trace followed by the literal j=0 declaration supplies
this loop's full initial model. All retained queries precede the real allocation. -/
theorem BufferOutput.write_model {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node heap payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput source current heap payload header) (data : ReferenceScanData source node)
    (keep : BitVec 64 → Prop) (earlier : ∀ query,keep query → query.toNat<heap.toNat)
    (aligned : heap.toNat%8=0) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    WriteModel source (bind current "j" 0#64) node heap stp pad data keep header (header+payload.toNat) 0
      (PersistentAlloc.rounded heap (BitVec.ofNat 64 (header+payload.toNat))) := by
  refine ⟨by decide,bind_lookup_same _ _ _,?_,?_,?_,output.heapCell,output.heapUpper,output.heapAligned,
    (by simpa only [Nat.add_assoc] using output.growth),(output.environment environment).of_frame rfl,output.runtime,?_,?_,output.metadata,output.globals⟩
  · exact (bind_lookup_other current "j" "node" 0#64 (by decide)).trans
      ((output.locals (ofString "node") (by decide) (by decide) (by decide)).trans nodeCell)
  · exact (bind_lookup_other current "j" "buf" 0#64 (by decide)).trans output.bufferCell
  · simpa only [ReferenceScanData.total,Nat.add_zero] using
      (bind_lookup_other current "j" "off" 0#64 (by decide)).trans output.offsetCell
  · intro query required
    exact output.before aligned query (earlier query required)
  · exact output.above_cap

/-- The actual branch value call reads its original160/168 fields and the
current destination formed by the real buffer and offset bindings. -/
theorem write_value_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) writeValueArguments=
      some [.val (.word (buffer+offset)),.val (.word view.pointer),.val (.word view.length)] := by
  simp [writeValueArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,bufferCell,offsetCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,view.pointerMapped,view.pointerStored,view.lengthMapped,view.lengthStored]

/-- Shared actual byte-writer call followed by its real offset update. -/
theorem bytes_update_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (arguments : List (ExpHOL 64)) (dst src count : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (small : count.toNat+32<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word count)]) :
    source.clock-(evaluateHOLFiniteState source (bytesStep name arguments)).2.clock≤Input.CopyAny.price count.toNat+21 := by
  obtain ⟨callee,called,d,s,n⟩:=Input.RlpWrite.BytesWrite.environment source.code.lookup dst src count (Input.CurrentRlp.BytesWrite.original_code source.code installed)
  have child:=Input.CurrentRlp.BytesWrite.body_known_length_cost (callEntryStateHOLFinite source callee) dst src count.toNat small installed domain d s
    (by change callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count.toNat))); simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using n)
  have priced:=Input.ClockCost.scoped_current source (ofString name) .one (ofString "rlp_encode_bytes") arguments _ Input.CurrentRlp.BytesWrite.body (addEncoded name)
    callee .one (Input.CopyAny.price count.toNat+20) 0 args called child (Input.ClockCost.assign source.code _ _)
  simpa only [bytesStep,Nat.add_zero,Nat.add_assoc] using priced

/-- The exact returned byte count, full destination frame and restored
caller locals for every genuine normal byte-writer/offset-update step. -/
theorem bytes_update_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (arguments : List (ExpHOL 64)) (dst src count first offset : BitVec 64)
    (other : ofString name≠ofString "off") (installed : Input.OriginalCode.Installed source.code) (small : count.toNat+32<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word count)])
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (firstRead : count=1#64 → eval source (.loadByte (.const src))=some (.val (.word first)))
    (normal : evaluateHOLFiniteState source (bytesStep name arguments)=(none,post)) :
    post.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 (Input.RlpLength.BytesSize.encodedLength first count)))) ∧
      Input.CurrentRlp.WriteFrame source post dst (Input.RlpLength.BytesSize.encodedLength first count) ∧
      ∀ key : MlS,key≠ofString "off" → post.locals.lookup key=source.locals.lookup key := by
  obtain ⟨funded,values,actualBody,callee,shape,childTarget,returned,inner,actualArgs,called,run,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_none_data source post name .one (ofString "rlp_encode_bytes") arguments (addEncoded name) normal
  let ready:=Input.CallNormal.continuationEntry source childTarget name returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "rlp_encode_bytes") arguments) ready:=
    .scoped source _ _ _ _ values actualBody callee shape returned childTarget actualArgs called (by omega) run checked
  obtain ⟨encoded,exactCount,_lower,_positive,_upper,_number,lengthCell,kept,frame⟩:=
    Input.CurrentRlp.BytesWrite.reached_span_normal_exact source ready (ofString name) arguments dst src count first installed small args firstRead reached
  have readyOffset : ready.locals.lookup (ofString "off")=some (.val (.word offset)):= (kept _ other).trans offsetCell
  have read : eval ready (.op .add [localVar "off",localVar name])=some (.val (.word (offset+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyOffset,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assigned:=Input.assign_none ready inner "off" (.op .add [localVar "off",localVar name]) (offset+BitVec.ofNat 64 encoded) read continued
  have finalFrame : Input.LocalEffects.erase post=Input.LocalEffects.erase ready:=by rw [endpoint,assigned]; rfl
  refine ⟨?_,?_,?_⟩
  · rw [endpoint,restore_lookup_other source inner name "off" (Ne.symm other),assigned,←exactCount]
    exact bind_lookup_same _ _ _
  · rw [←exactCount]
    exact ⟨(Input.MemoryMetadata.of_frame finalFrame).trans frame.metadata,
      fun query away=>(congrFun (Input.LocalEffects.memory_of_erase ready post finalFrame) query).trans (frame.memory query away)⟩
  · intro key different
    rw [endpoint]
    by_cases resultKey : key=ofString name
    · subst key
      change (HolFiniteMapExact.resVarEq inner.locals (ofString name,source.locals.lookup (ofString name))).lookup (ofString name)=_
      rw [lookup_resVarEq_toExact]
      cases source.locals.lookup (ofString name) <;> simp [resVarHOLExact]
    · have restored : (restore source name inner).locals.lookup key=inner.locals.lookup key:=by
        change (HolFiniteMapExact.resVarEq inner.locals (ofString name,source.locals.lookup (ofString name))).lookup key=_
        rw [lookup_resVarEq_toExact]
        cases source.locals.lookup (ofString name) <;> simp [resVarHOLExact,resultKey]
      rw [restored,assigned]
      have binding : (bind ready "off" (offset+BitVec.ofNat 64 encoded)).locals.lookup key=ready.locals.lookup key:=by
        simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
      exact binding.trans (kept key (Ne.symm resultKey))

/-- A finite all-outcomes allowance for the real value writer plus its
scoped offset update; failed stores remain included. -/
theorem write_value_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (small : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    source.clock-(evaluateHOLFiniteState source afterWrites).2.clock≤Input.CopyAny.price view.length.toNat+21 := by
  rw [write_value_shape]
  exact bytes_update_cost source "w5" writeValueArguments (buffer+offset) view.pointer view.length installed domain small
    (write_value_arguments source node buffer offset limit property view nodeCell bufferCell offsetCell)

/-- A genuine value write returns the exact previously computed encoded
length and then performs its actual offset assignment and scope restoration. -/
theorem write_value_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset first : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (small : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (firstRead : view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (normal : evaluateHOLFiniteState source afterWrites=(none,post)) :
    post.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 (Input.RlpLength.BytesSize.encodedLength first view.length)))) ∧
      Input.CurrentRlp.WriteFrame source post (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first view.length) ∧
      ∀ key : MlS,key≠ofString "off" → post.locals.lookup key=source.locals.lookup key := by
  have shaped:=normal
  rw [write_value_shape] at shaped
  exact bytes_update_normal source post "w5" writeValueArguments (buffer+offset) view.pointer view.length first offset (by decide) installed small
    (write_value_arguments source node buffer offset limit property view nodeCell bufferCell offsetCell) offsetCell firstRead shaped


/-- The loop's retained physical value words supply the actual value view
at its reached continuation, without assuming later reads. -/
def WriteModel.value_view {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap)
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 limit property)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64)) :
    TrieWalk.ValueView current.memory current.memaddrs node 160#64 168#64 limit property :=
  view.of_agreement origin.memory current.memory origin.memaddrs current.memaddrs node 160#64 168#64 limit model.runtime.1
    (model.memory _ pointerKept) (model.memory _ lengthKept)

/-- A kept backing word and the actual retained domain/endian fields
transport the same one-byte decision from the earlier sizing phase. -/
theorem WriteModel.byte_read {origin current : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span i : Nat} {heap : BitVec 64}
    (model : WriteModel origin current node buffer stp pad data keep start span i heap) (pointer first : BitVec 64)
    (required : keep (panByteAlignHOL (width:=64) pointer))
    (read : eval origin (.loadByte (.const pointer))=some (.val (.word first))) :
    eval current (.loadByte (.const pointer))=some (.val (.word first)) := by
  classical
  have memory:=model.memory _ required
  have same : @panMemLoadByteHOL 64 _ current.memory current.memaddrs
      (fun query=>Classical.propDecidable (current.memaddrs query)) current.be pointer=
      @panMemLoadByteHOL 64 _ origin.memory origin.memaddrs
      (fun query=>Classical.propDecidable (origin.memaddrs query)) origin.be pointer:=by
    dsimp only [panMemLoadByteHOL]
    rw [model.runtime.1,model.runtime.2.1]
    exact congrArg (fun cell : HolWordLab 64=>match cell with
      | .word word=>if origin.memaddrs (panByteAlignHOL (width:=64) pointer) then some (panGetByteHOL pointer word origin.be) else none) memory
  change Option.map (fun value : UInt8=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 value.toNat)))
    (@panMemLoadByteHOL 64 _ current.memory current.memaddrs (fun query=>Classical.propDecidable (current.memaddrs query)) current.be pointer)=_
  rw [same]
  exact read

/-- The entire reached branch-writing sequence, including the actual value
call, has a current-state bound. Its value fields come from normal loop effects. -/
theorem write_loop_value_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span initial : Nat} {heap : BitVec 64}
    (model : WriteModel origin source node buffer stp pad data keep start span initial heap)
    (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat) (budget : start+data.total 16≤span)
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (limit : Nat) (lengths : ∀ j,j<16 → (data.length j).toNat≤limit)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64)) (valueSmall : view.length.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source (.seq writeLoop afterWrites)).2.clock≤
      (CurrentKeccak.Hash.boundedBodyPrice limit+48)*(16-initial)+Input.CopyAny.price view.length.toNat+21 := by
  have result:=Input.ClockCost.sequence_reached_current source writeLoop afterWrites
    ((CurrentKeccak.Hash.boundedBodyPrice limit+48)*(16-initial)) (Input.CopyAny.price view.length.toNat+21)
    (write_loop_cost model aligned bufferLower budget protection covers limit lengths digestMapped) (by
      intro current normal
      obtain ⟨nextHeap,next⟩:=write_loop_normal model aligned bufferLower budget protection covers
        digestMapped normal
      exact write_value_cost current node buffer (BitVec.ofNat 64 (start+data.total 16)) valueLimit property
        (next.value_view view pointerKept lengthKept) next.environment.installed next.environment.domain valueSmall next.nodeCell next.bufferCell next.offsetCell)
  simpa only [Nat.add_assoc] using result

/-- A genuine normal completion of the branch-writing sequence reaches
the exact allocation end computed before writing any child or value. -/
theorem write_loop_value_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    {data : ReferenceScanData origin node} {keep : BitVec 64 → Prop} {start span initial : Nat} {heap : BitVec 64}
    (model : WriteModel origin source node buffer stp pad data keep start span initial heap)
    (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat) (budget : start+data.total 16≤span)
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property) (first : BitVec 64)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64))
    (byteKept : view.length=1#64 → keep (panByteAlignHOL (width:=64) view.pointer)) (valueSmall : view.length.toNat+32<2^64)
    (firstRead : view.length=1#64 → eval origin (.loadByte (.const view.pointer))=some (.val (.word first)))
    (exactSpan : span=start+data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length)
    (normal : evaluateHOLFiniteState source (.seq writeLoop afterWrites)=(none,post)) :
    ∃ current nextHeap,WriteModel origin current node buffer stp pad data keep start span 16 nextHeap ∧
      post.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 span))) ∧
      Input.CurrentRlp.WriteFrame current post (buffer+BitVec.ofNat 64 (start+data.total 16)) (Input.RlpLength.BytesSize.encodedLength first view.length) ∧
      ∀ key : MlS,key≠ofString "off" → post.locals.lookup key=current.locals.lookup key := by
  obtain ⟨current,loopRun,valueRun⟩:=Input.sequence_none source post writeLoop afterWrites normal
  obtain ⟨nextHeap,next⟩:=write_loop_normal model aligned bufferLower budget protection covers digestMapped loopRun
  let currentView:=next.value_view view pointerKept lengthKept
  have byteRead : currentView.length=1#64 → eval current (.loadByte (.const currentView.pointer))=some (.val (.word first)):=by
    intro one
    exact next.byte_read view.pointer first (byteKept one) (firstRead one)
  obtain ⟨offset,frame,locals⟩:=write_value_normal current post node buffer (BitVec.ofNat 64 (start+data.total 16)) first valueLimit property
    currentView next.environment.installed valueSmall next.nodeCell next.bufferCell next.offsetCell byteRead valueRun
  refine ⟨current,nextHeap,next,?_,frame,locals⟩
  rw [exactSpan,BitVec.ofNat_add]
  exact offset

/-- The literal branch scope initializes j=0 from the real buffer prefix,
then prices its complete reference-and-value writing sequence. -/
theorem BufferOutput.branch_writes_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ReferenceScanData origin node)
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat)
    (environment : CurrentKeccak.Hash.Environment origin stp pad) (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (budget : data.total 16≤payload.toNat) (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (limit : Nat) (lengths : ∀ j,j<16 → (data.length j).toNat≤limit)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64)) (valueSmall : view.length.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source branchWriteScope).2.clock≤
      (CurrentKeccak.Hash.boundedBodyPrice limit+48)*16+Input.CopyAny.price view.length.toNat+21 := by
  rw [write_shapes.2.2.1]
  apply Input.ClockCost.declared_current source "j" (.const 0#64) 0#64 (.seq writeLoop afterWrites) _ rfl
  exact write_loop_value_cost (output.write_model data keep protection.earlier aligned environment nodeCell) aligned bufferLower
    (by omega) protection covers limit lengths digestMapped view pointerKept lengthKept valueSmall

/-- The two literal cache stores and return spend no source call/loop ticks. -/
theorem footer_cost (code) : Input.ClockCost.Bound code footer 0 := by
  rw [footer_shape]
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.returned code _))

/-- The actual footer installs the serialized pointer and exact final size
using existing mapped node words, retaining all other memory and runtime state. -/
theorem footer_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer length : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word length)))
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64)) :
    evaluateHOLFiniteState source footer=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=StoreWord.put (StoreWord.put source.memory (node+8#64) buffer) (node+16#64) length}) := by
  let first : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (node+8#64) buffer}
  have one:=StoreWord.execute source (.op .add [localVar "node",.const 8#64]) (localVar "buf") (node+8#64) buffer
    (by simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp])
    (by simpa only [eval,evalHOLExact,toExact,localVar] using bufferCell) pointerMapped
  have two:=StoreWord.execute first (.op .add [localVar "node",.const 16#64]) (localVar "off") (node+16#64) length
    (by simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,first,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp])
    (by simpa only [eval,evalHOLExact,toExact,localVar,first] using offsetCell) lengthMapped
  rw [footer_shape,evaluateHOLFiniteState_seq_line780,one]
  change evaluateHOLFiniteState first (.seq (.store (.op .add [localVar "node",.const 16#64]) (localVar "off")) (.return (.const 0#64)))=_
  rw [evaluateHOLFiniteState_seq_line780,two]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,first]


/-- The real j scope cannot return its caller; both helper calls are scoped. -/
theorem branch_write_safe : Input.LocalPrefix (ofString "node") branchWriteScope := by
  rw [write_shapes.2.2.1]
  apply Input.LocalPrefix.dec _ _ _ (by decide)
  apply Input.LocalPrefix.seq
  · rw [write_shapes.2.2.2.1]
    exact Input.LocalPrefix.loop writeTest (write_body_safe _ (by decide) (by decide) (by decide))
  · rw [write_value_shape]
    exact Input.LocalPrefix.decCall _ _ _ _ (by decide) (Input.LocalPrefix.assign _ _ (by decide))

/-- Branch selection and the literal footer add no source ticks beyond the
actual writing scope priced from its physical buffer-prefix output. -/
theorem BufferOutput.writer_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ReferenceScanData origin node)
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat)
    (environment : CurrentKeccak.Hash.Environment origin stp pad) (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (budget : data.total 16≤payload.toNat) (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (limit : Nat) (lengths : ∀ j,j<16 → (data.length j).toNat≤limit)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64)) (valueSmall : view.length.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source writerTail).2.clock≤
      (CurrentKeccak.Hash.boundedBodyPrice limit+48)*16+Input.CopyAny.price view.length.toNat+21 := by
  have selected : evaluateHOLFiniteState source writeChoice=evaluateHOLFiniteState source branchWriteScope:=by
    rw [write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have price:=output.branch_writes_cost data keep aligned bufferLower environment nodeCell budget protection covers limit lengths digestMapped
    view pointerKept lengthKept valueSmall
  have choicePrice : source.clock-(evaluateHOLFiniteState source writeChoice).2.clock≤
      (CurrentKeccak.Hash.boundedBodyPrice limit+48)*16+Input.CopyAny.price view.length.toNat+21:=by rw [selected]; exact price
  rw [write_shapes.1]
  have total:=Input.ClockCost.sequence_current source writeChoice footer _ 0 choicePrice (footer_cost source.code)
  simpa only [Nat.add_zero] using total

/-- The actual branch writer return derives its full loop model, exact
value span, actual footer state and successful cache stores from one run. -/
theorem BufferOutput.writer_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ReferenceScanData origin node)
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0) (bufferLower : 2701131776≤buffer.toNat)
    (environment : CurrentKeccak.Hash.Environment origin stp pad) (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property) (first : BitVec 64)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64))
    (byteKept : view.length=1#64 → keep (panByteAlignHOL (width:=64) view.pointer)) (valueSmall : view.length.toNat+32<2^64)
    (firstRead : view.length=1#64 → eval origin (.loadByte (.const view.pointer))=some (.val (.word first)))
    (exactPayload : payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length)
    (pointerMapped : origin.memaddrs (node+8#64)) (lengthMapped : origin.memaddrs (node+16#64))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source writerTail=(some (.returned value),post)) :
    ∃ current written nextHeap,WriteModel origin current node buffer stp pad data keep header (header+payload.toNat) 16 nextHeap ∧
      Input.CurrentRlp.WriteFrame current written (buffer+BitVec.ofNat 64 (header+data.total 16)) (Input.RlpLength.BytesSize.encodedLength first view.length) ∧
      written.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (header+payload.toNat)))) ∧
      written.locals.lookup (ofString "node")=some (.val (.word node)) ∧ written.locals.lookup (ofString "buf")=some (.val (.word buffer)) ∧
      post=emptyLocalsHOLFinite {written with memory:=StoreWord.put (StoreWord.put written.memory (node+8#64) buffer) (node+16#64) (BitVec.ofNat 64 (header+payload.toNat))} ∧
      value=.val (.word 0#64) := by
  have selected : evaluateHOLFiniteState source writeChoice=evaluateHOLFiniteState source branchWriteScope:=by
    rw [write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have shaped : evaluateHOLFiniteState source (.seq branchWriteScope footer)=(some (.returned value),post):=by
    rw [write_shapes.1,evaluateHOLFiniteState_seq_line780,selected] at normal
    rw [evaluateHOLFiniteState_seq_line780]
    exact normal
  obtain ⟨written,scopeRun,footerRun⟩:=Input.sequence_returned source post branchWriteScope footer value (branch_write_safe.summary_full source).2.1 shaped
  rw [write_shapes.2.2.1] at scopeRun
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source written "j" (.const 0#64) 0#64 (.seq writeLoop afterWrites) rfl scopeRun
  have model:=output.write_model data keep protection.earlier aligned environment nodeCell
  obtain ⟨current,nextHeap,next,offset,frame,locals⟩:=write_loop_value_normal model aligned bufferLower
    (by omega) protection covers digestMapped view first pointerKept lengthKept byteKept valueSmall firstRead
    (by rw [exactPayload,Nat.add_assoc]) continued
  have writtenOffset : written.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (header+payload.toNat)))):=by
    rw [endpoint,restore_lookup_other source inner "j" "off" (by decide)]
    exact offset
  have writtenNode : written.locals.lookup (ofString "node")=some (.val (.word node)):=by
    rw [endpoint,restore_lookup_other source inner "j" "node" (by decide)]
    exact (locals _ (by decide)).trans next.nodeCell
  have writtenBuffer : written.locals.lookup (ofString "buf")=some (.val (.word buffer)):=by
    rw [endpoint,restore_lookup_other source inner "j" "buf" (by decide)]
    exact (locals _ (by decide)).trans next.bufferCell
  have writtenFrame : Input.CurrentRlp.WriteFrame current written (buffer+BitVec.ofNat 64 (header+data.total 16))
      (Input.RlpLength.BytesSize.encodedLength first view.length):=by
    rw [endpoint]
    exact ⟨frame.metadata,frame.memory⟩
  have domain : written.memaddrs=origin.memaddrs:=(Input.MemoryMetadata.domain writtenFrame.metadata).trans next.runtime.1
  have actual:=footer_execute written node buffer (BitVec.ofNat 64 (header+payload.toNat)) writtenNode writtenBuffer writtenOffset
    (by rw [domain]; exact pointerMapped) (by rw [domain]; exact lengthMapped)
  have same:=footerRun.symm.trans actual
  exact ⟨current,written,nextHeap,next,writtenFrame,writtenOffset,writtenNode,writtenBuffer,congrArg Prod.snd same,
    PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))⟩


/-- Physical registered node words other than the mutable HASH24 field. -/
def RegisteredField {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (graph : TrieWalk.Graph source.memory source.memaddrs) (query : BitVec 64) : Prop :=
  ∃ owner offset,graph.valid owner ∧ owner≠0#64 ∧ offset<TrieWalk.nodeBytes (GasBudget.wordAt source.memory owner) ∧ offset≠24 ∧ query=byteAddress owner offset

/-- Existing node fields and earlier input words kept through child hashing. -/
def BranchQueries {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (graph : TrieWalk.Graph source.memory source.memaddrs) (inputEnd : Nat) (query : BitVec 64) : Prop :=
  RegisteredField graph query ∨ (2701134824≤query.toNat ∧ query.toNat<inputEnd)

theorem ReferenceScanData.branch_queries {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : GasBudget.wordAt source.memory node=3#64) (inputEnd : Nat)
    (query : BitVec 64) (required : data.Footprint query) : BranchQueries graph inputEnd query :=
  Or.inl (required.location data graph member active tag query)

/-- Derive the writer's full separation conditions from genuine node
allocation regions/disjointness and the earlier input/workspace layout.
No later hash, store or allocation success is assumed. -/
theorem WriteProtection.of_graph {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    (data : ReferenceScanData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : GasBudget.wordAt source.memory node=3#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (beforeBuffer : upper≤buffer.toNat) (belowCap : upper≤2952790016)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824) :
    WriteProtection data.child buffer stp pad (BranchQueries graph inputEnd) := by
  have parent:=regions node member active
  have nodeSize:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory node)
  have ordered : lower≤upper:=by omega
  have stateCap : stp.toNat+200≤2952790016:=by omega
  have padCap : pad.toNat+136≤2952790016:=by omega
  have queryBounds : ∀ query,RegisteredField graph query → lower≤query.toNat ∧ query.toNat<upper:=by
    intro query ⟨owner,offset,ownerMember,live,inside,_notCache,equal⟩
    rw [equal]
    exact graph.region_query_bounds lower upper regions owner offset ownerMember live inside
  refine ⟨?_,?_,?_,?_,?_,stateCap,padCap⟩
  · intro query required
    rcases required with field|input
    · have bound:=queryBounds query field; omega
    · omega
  · intro query required
    rcases required with field|input
    · have bound:=queryBounds query field
      exact CopyGeneral.Away.before stp query 200 (stp.toNat+200) (Nat.le_refl _) (by have aligned:=environment.stateAligned; omega) (by omega)
    · exact CopyGeneral.Away.before stp query 200 2701134824 stateBeforeInput (by decide) input.1
  · intro query required
    rcases required with field|input
    · have bound:=queryBounds query field
      exact CopyGeneral.Away.before pad query 136 (pad.toNat+136) (Nat.le_refl _) (by have aligned:=environment.padAligned; omega) (by omega)
    · exact CopyGeneral.Away.before pad query 136 2701134824 padBeforeInput (by decide) input.1
  · intro i inside live query required
    have childMember:=data.child_member graph member active tag i inside
    rcases required with ⟨owner,offset,ownerMember,ownerLive,within,notCache,equal⟩|input
    · rw [equal]
      exact graph.cache_away lower upper regions disjoint (data.child i) owner offset childMember live ownerMember ownerLive within notCache
    · have childRegion:=regions (data.child i) childMember live
      have number : (data.child i+24#64).toNat=(data.child i).toNat+24:=
        byteAddress_toNat (data.child i) 24 (by have cap:=childRegion.2.1.upper; have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i)); omega)
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number] at numeric
      omega
  · intro i inside
    by_cases null : data.child i=0#64
    · rw [null]; decide
    · have childMember:=data.child_member graph member active tag i inside
      have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i))
      have bounds:=graph.region_query_bounds lower upper regions (data.child i) 24 childMember null (by omega)
      change lower≤(data.child i+24#64).toNat ∧ (data.child i+24#64).toNat<upper at bounds
      omega


/-- Obtain the complete actual branch writer allowance from its registered
graph, existing physical layout and bounded populated caches. The reference
data, cache mapping, query coverage and write separation are all derived. -/
theorem BufferOutput.writer_cost_of_graph {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header)
    (graph : TrieWalk.Graph origin.memory origin.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt origin.memory node=3#64) (lower upper inputEnd : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (environment : CurrentKeccak.Hash.Environment origin stp pad)
    (aligned : buffer.toNat%8=0) (beforeBuffer : upper≤buffer.toNat) (belowCap : upper≤2952790016)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (budget : (ReferenceScanData.of_graph origin node graph member active tag lower upper regions environment.domain).total 16≤payload.toNat)
    (limit : Nat) (bounded : CachedLengths graph limit)
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property)
    (valueSmall : view.length.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source writerTail).2.clock≤
      (CurrentKeccak.Hash.boundedBodyPrice limit+48)*16+Input.CopyAny.price view.length.toNat+21 := by
  let data:=ReferenceScanData.of_graph origin node graph member active tag lower upper regions environment.domain
  have protection:=WriteProtection.of_graph data graph member active tag lower upper inputEnd regions disjoint environment beforeBuffer belowCap
    stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
  have pointerKept : BranchQueries graph inputEnd (node+160#64):=by
    refine Or.inl ⟨node,160,member,active,?_,by decide,rfl⟩
    rw [tag]; decide
  have lengthKept : BranchQueries graph inputEnd (node+168#64):=by
    refine Or.inl ⟨node,168,member,active,?_,by decide,rfl⟩
    rw [tag]; decide
  apply output.writer_cost data (BranchQueries graph inputEnd) aligned output.arena.lower environment nodeCell tagCell budget protection
    (data.branch_queries graph member active tag inputEnd) limit
    (ReferenceScanData.of_graph_lengths origin node graph member active tag lower upper regions environment.domain limit bounded)
    (by
      intro i inside live _nonHash _populated
      exact reference_cache_mapped origin graph lower upper regions environment.domain (data.child i)
        (data.child_member graph member active tag i inside) live 24 (by decide) (by decide))
    view pointerKept lengthKept valueSmall


/-- A completed real finish writer has installed its exact node cache and
retains every selected source query except its two actual footer destinations. -/
structure FinishOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer : BitVec 64)
    (bytes : Nat) (keep : BitVec 64 → Prop) : Prop where
  pointerStored : post.memory (node+8#64)=.word buffer
  lengthStored : post.memory (node+16#64)=.word (BitVec.ofNat 64 bytes)
  heap : ∃ next,post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧ next.toNat≤2952790016 ∧ next.toNat%8=0 ∧ buffer.toNat+bytes≤next.toNat
  runtime : post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code
  metadata : Rlp.Validation.scratchMetadata post=Rlp.Validation.scratchMetadata source
  globals : HeapGlobals source post
  memory : ∀ query,keep query → query≠node+8#64 → query≠node+16#64 → post.memory query=source.memory query
  scratch : ∀ query,2952790016≤query.toNat → post.memory query=source.memory query

/-- Retain a selected subset of an actual completed writer's query frame. -/
theorem FinishOutput.weaken_keep {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat}
    {keep smaller : BitVec 64 → Prop} (output : FinishOutput source post node buffer bytes keep)
    (covers : ∀ query,smaller query → keep query) : FinishOutput source post node buffer bytes smaller :=
  ⟨output.pointerStored,output.lengthStored,output.heap,output.runtime,output.metadata,output.globals,
    fun query required=>output.memory query (covers query required),output.scratch⟩

/-- Actual completed writing, before the two literal node-cache stores.
This common physical contract permits real reference hashing and heap growth. -/
structure WrittenOutput (source written : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (bytes : Nat) (keep : BitVec 64 → Prop) : Prop where
  heap : ∃ next,written.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧ next.toNat≤2952790016 ∧ next.toNat%8=0 ∧ buffer.toNat+bytes≤next.toNat
  runtime : written.memaddrs=source.memaddrs ∧ written.be=source.be ∧ written.code=source.code
  metadata : Rlp.Validation.scratchMetadata written=Rlp.Validation.scratchMetadata source
  globals : HeapGlobals source written
  memory : ∀ query,keep query → written.memory query=source.memory query
  scratch : ∀ query,2952790016≤query.toNat → written.memory query=source.memory query

/-- Connect an observed completed writer to the real cache footer once,
sharing its exact memory, heap and lexical-return bookkeeping. -/
theorem WrittenOutput.footer {source written post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : WrittenOutput source written buffer bytes keep)
    (nodeCell : written.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : written.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : written.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 bytes))))
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64))
    (nodeBefore : node.toNat+24≤2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState written footer=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ FinishOutput source post node buffer bytes keep := by
  have actual:=footer_execute written node buffer (BitVec.ofNat 64 bytes) nodeCell bufferCell offsetCell
    (by rw [output.runtime.1]; exact pointerMapped) (by rw [output.runtime.1]; exact lengthMapped)
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (normal.symm.trans actual)))
  have endpoint:=congrArg Prod.snd (normal.symm.trans actual)
  dsimp only [Prod.snd] at endpoint
  have afterFooter (query : BitVec 64) (pointerAway : query≠node+8#64) (lengthAway : query≠node+16#64) : post.memory query=written.memory query:=by
    rw [endpoint]
    exact (if_neg lengthAway).trans (if_neg pointerAway)
  refine ⟨answer,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [endpoint]
    change StoreWord.put (StoreWord.put written.memory (node+8#64) buffer) (node+16#64) (BitVec.ofNat 64 bytes) (node+8#64)=.word buffer
    simp [StoreWord.put,GasBudget.offsets_ne node 8#64 16#64 (by decide)]
  · rw [endpoint]
    exact if_pos rfl
  · rw [endpoint]
    exact output.heap
  · rw [endpoint]
    exact output.runtime
  · rw [endpoint]
    exact output.metadata
  · rw [endpoint]
    exact output.globals
  · intro query required pointerAway lengthAway
    exact (afterFooter query pointerAway lengthAway).trans (output.memory query required)
  · intro query above
    have pointerNumber : (node+8#64).toNat=node.toNat+8:=byteAddress_toNat node 8 (by omega)
    have lengthNumber : (node+16#64).toNat=node.toNat+16:=byteAddress_toNat node 16 (by omega)
    have pointerAway : query≠node+8#64:=by intro same; rw [same,pointerNumber] at above; omega
    have lengthAway : query≠node+16#64:=by intro same; rw [same,lengthNumber] at above; omega
    exact (afterFooter query pointerAway lengthAway).trans (output.scratch query above)


/-- Observe the complete normal branch writer once, composing its actual
loop model, exact value span, restored scope and final cache stores. -/
theorem BufferOutput.finish_output {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ReferenceScanData origin node)
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0)
    (environment : CurrentKeccak.Hash.Environment origin stp pad) (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (protection : WriteProtection data.child buffer stp pad keep) (covers : ∀ query,data.Footprint query → keep query)
    (digestMapped : ∀ j,j<16 → data.child j≠0#64 → data.tag j≠0#64 → data.cached j≠0#64 → origin.memaddrs (data.child j+24#64))
    {valueLimit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 160#64 168#64 valueLimit property) (first : BitVec 64)
    (pointerKept : keep (node+160#64)) (lengthKept : keep (node+168#64))
    (byteKept : view.length=1#64 → keep (panByteAlignHOL (width:=64) view.pointer)) (valueSmall : view.length.toNat+32<2^64)
    (firstRead : view.length=1#64 → eval origin (.loadByte (.const view.pointer))=some (.val (.word first)))
    (exactPayload : payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length)
    (pointerMapped : origin.memaddrs (node+8#64)) (lengthMapped : origin.memaddrs (node+16#64)) (nodeBefore : node.toNat+24≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source writerTail=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ FinishOutput origin post node buffer (header+payload.toNat) keep := by
  obtain ⟨current,written,nextHeap,model,frame,writtenOffset,writtenNode,writtenBuffer,endpoint,answer⟩:=output.writer_normal data keep aligned output.arena.lower environment nodeCell tagCell
    protection covers digestMapped view first pointerKept lengthKept byteKept valueSmall firstRead exactPayload pointerMapped lengthMapped value normal
  let amount:=Input.RlpLength.BytesSize.encodedLength first view.length
  let offset:=BitVec.ofNat 64 (header+data.total 16)
  have room:=output.room
  have offsetNumber : offset.toNat=header+data.total 16:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have dstNumber : (buffer+offset).toNat=buffer.toNat+header+data.total 16:=by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega),offsetNumber,Nat.add_assoc]
  have writtenGlobals:=congrArg PanSemStateFiniteExact.globals frame.metadata
  change written.globals=current.globals at writtenGlobals
  have physical : written.memaddrs=origin.memaddrs ∧ written.be=origin.be ∧ written.code=origin.code:=
    ⟨(Input.MemoryMetadata.domain frame.metadata).trans model.runtime.1,
      (Input.MemoryMetadata.endian frame.metadata).trans model.runtime.2.1,
      (Input.MemoryMetadata.code frame.metadata).trans model.runtime.2.2⟩
  have metadata : Rlp.Validation.scratchMetadata written=Rlp.Validation.scratchMetadata origin:=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) frame.metadata).trans model.metadata
  have valueMemory : ∀ query,keep query → written.memory query=origin.memory query:=by
    intro query required
    have earlier:=protection.earlier query required
    have away : CopyGeneral.Away (buffer+offset) query amount:=CopyGeneral.Away.after_floor (buffer+offset) query amount buffer.toNat aligned
      (by rw [dstNumber]; omega) (by rw [dstNumber]; change buffer.toNat+header+data.total 16+amount<2^64; omega) earlier
    exact (frame.memory query away).trans (model.memory query required)
  have highValue : ∀ query,2952790016≤query.toNat → written.memory query=origin.memory query:=by
    intro query above
    have away : CopyGeneral.Away (buffer+offset) query amount:=CopyGeneral.Away.before (buffer+offset) query amount 2952790016
      (by rw [dstNumber]; change buffer.toNat+header+data.total 16+amount≤2952790016; omega) (by decide) above
    exact (frame.memory query away).trans (model.scratch query above)
  have completed : WrittenOutput origin written buffer (header+payload.toNat) keep:=by
    refine ⟨⟨nextHeap,by rw [writtenGlobals]; exact model.heapCell,model.heapUpper,model.heapAligned,model.heapFloor⟩,
      physical,metadata,?_,valueMemory,highValue⟩
    intro key different
    rw [writtenGlobals]
    exact model.globals key different
  have footerRun : evaluateHOLFiniteState written footer=(some (.returned value),post):=by
    rw [answer,endpoint]
    exact footer_execute written node buffer (BitVec.ofNat 64 (header+payload.toNat)) writtenNode writtenBuffer writtenOffset
      (by rw [physical.1]; exact pointerMapped) (by rw [physical.1]; exact lengthMapped)
  exact completed.footer writtenNode writtenBuffer writtenOffset pointerMapped lengthMapped nodeBefore value footerRun


/-- Any two fields in distinct live registered allocations are separate,
including both nodes' metadata caches. -/
theorem registered_fields_apart (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (first second : BitVec 64) (a b : Nat) (firstMember : graph.valid first) (firstActive : first≠0#64)
    (secondMember : graph.valid second) (secondActive : second≠0#64) (different : first≠second)
    (firstInside : a<TrieWalk.nodeBytes (GasBudget.wordAt source.memory first))
    (secondInside : b<TrieWalk.nodeBytes (GasBudget.wordAt source.memory second)) : byteAddress first a≠byteAddress second b := by
  have firstRegion:=regions first firstMember firstActive
  have secondRegion:=regions second secondMember secondActive
  have separated:=disjoint first firstMember firstActive second secondMember secondActive different
  have firstNumber:=byteAddress_toNat first a (by have cap:=firstRegion.2.1.upper; omega)
  have secondNumber:=byteAddress_toNat second b (by have cap:=secondRegion.2.1.upper; omega)
  intro equal
  have numeric:=congrArg BitVec.toNat equal
  rw [firstNumber,secondNumber] at numeric
  omega

/-- A real completed writer retains all registered data fields; its two
footer cache destinations are disjoint from those same-owner/other-owner fields. -/
theorem FinishOutput.data_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (covers : ∀ query,RegisteredField graph query → keep query)
    (owner : BitVec 64) (offset : Nat) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (inside : offset<TrieWalk.nodeBytes (GasBudget.wordAt source.memory owner)) (dataOffset : offset=0 ∨ 32≤offset) :
    post.memory (byteAddress owner offset)=source.memory (byteAddress owner offset) :=
  output.memory _ (covers _ ⟨owner,offset,ownerMember,ownerActive,inside,by omega,rfl⟩)
    (graph.cache_field_away lower upper regions disjoint node owner offset 8 (by decide) (by decide) member active ownerMember ownerActive inside dataOffset)
    (graph.cache_field_away lower upper regions disjoint node owner offset 16 (by decide) (by decide) member active ownerMember ownerActive inside dataOffset)

/-- A real completed writer reconstructs the same registered graph and
values. Its exact newly installed cache length and retained older cache
words preserve a uniform populated-cache bound. -/
theorem FinishOutput.after_graph {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (covers : ∀ query,RegisteredField graph query → keep query)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop) (values : TrieWalk.Values graph valueLimit property)
    (limit : Nat) (bounded : CachedLengths graph limit) (newBound : bytes≤limit) :
    ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (TrieWalk.Values next valueLimit property) ∧ CachedLengths next limit := by
  have dataMemory:=output.data_memory graph member active lower upper regions disjoint covers
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    obtain ⟨owner,offset,ownerMember,ownerActive,inside,dataOffset,equal⟩:=required.data_location graph query
    rw [equal]
    exact dataMemory owner offset ownerMember ownerActive inside dataOffset
  have valueAgree : ∀ query,TrieWalk.ValueFootprint graph query → post.memory query=source.memory query:=by
    intro query required
    obtain ⟨owner,offset,ownerMember,ownerActive,inside,dataOffset,equal⟩:=required.data_location graph query
    rw [equal]
    exact dataMemory owner offset ownerMember ownerActive inside dataOffset
  have tags : ∀ owner,graph.valid owner → owner≠0#64 → GasBudget.wordAt post.memory owner=GasBudget.wordAt source.memory owner:=by
    intro owner ownerMember ownerActive
    unfold GasBudget.wordAt
    rw [agree owner (.header owner ownerMember ownerActive)]
  let next:=TrieWalk.Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph output.runtime.1 agree
  have same : next.valid=graph.valid:=rfl
  refine ⟨next,same,regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next lower upper same tags,
    disjoint.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next same tags,
    ⟨TrieWalk.Values.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next valueLimit values same output.runtime.1 tags valueAgree⟩,?_⟩
  intro owner ownerMember ownerActive nonHash populated
  have oldMember : graph.valid owner:=ownerMember
  by_cases own : owner=node
  · subst owner
    change (GasBudget.wordAt post.memory (node+16#64)).toNat≤limit
    simp only [GasBudget.wordAt,output.lengthStored,MemoryBytes.wordBits,BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le bytes _) newBound
  · have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory owner)
    have nodeMinimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory node)
    have cacheMemory : ∀ offset : Nat,(offset=8 ∨ offset=16) → post.memory (byteAddress owner offset)=source.memory (byteAddress owner offset):=by
      intro offset selected
      have inside : offset<TrieWalk.nodeBytes (GasBudget.wordAt source.memory owner):=by rcases selected with rfl|rfl <;> omega
      have notHashCache : offset≠24:=by rcases selected with rfl|rfl <;> decide
      exact output.memory _ (covers _ ⟨owner,offset,oldMember,ownerActive,inside,notHashCache,rfl⟩)
        (registered_fields_apart source graph lower upper regions disjoint owner node offset 8 oldMember ownerActive member active own inside (by omega))
        (registered_fields_apart source graph lower upper regions disjoint owner node offset 16 oldMember ownerActive member active own inside (by omega))
    have cache8:=cacheMemory 8 (Or.inl rfl)
    change post.memory (owner+8#64)=source.memory (owner+8#64) at cache8
    have cache16:=cacheMemory 16 (Or.inr rfl)
    change post.memory (owner+16#64)=source.memory (owner+16#64) at cache16
    have oldNonHash : GasBudget.wordAt source.memory owner≠0#64:=by rw [←tags owner oldMember ownerActive]; exact nonHash
    have oldPopulated : GasBudget.wordAt source.memory (owner+8#64)≠0#64:=by
      change MemoryBytes.wordBits (source.memory (owner+8#64))≠0#64
      rw [←cache8]
      exact populated
    change (GasBudget.wordAt post.memory (owner+16#64)).toNat≤limit
    unfold GasBudget.wordAt
    rw [cache16]
    exact bounded owner oldMember ownerActive oldNonHash oldPopulated


/-- Actual backing words of all existing leaf/extension nibble paths. -/
def PathQuery {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (graph : TrieWalk.Graph source.memory source.memaddrs) (query : BitVec 64) : Prop :=
  ∃ owner,graph.valid owner ∧ owner≠0#64 ∧ (GasBudget.wordAt source.memory owner=1#64 ∨ GasBudget.wordAt source.memory owner=2#64) ∧
    ∃ index,index<(GasBudget.wordAt source.memory (owner+40#64)).toNat ∧
      query=panByteAlignHOL (width:=64) (byteAddress (GasBudget.wordAt source.memory (owner+32#64)) index)

/-- The same original graph paths are needed after a branch finishes. -/
def SerializerQueries {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (graph : TrieWalk.Graph source.memory source.memaddrs) (inputEnd : Nat) (query : BitVec 64) : Prop :=
  BranchQueries graph inputEnd query ∨ PathQuery graph query

/-- Existing path layout and node separation extend the already derived
branch protection to full stored paths, including unaligned borrowed slices. -/
theorem WriteProtection.with_paths {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    (data : ReferenceScanData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : GasBudget.wordAt source.memory node=3#64)
    (inputEnd : Nat) (protection : WriteProtection data.child buffer stp pad (BranchQueries graph inputEnd))
    (paths : graph.PathBytes source.be) (lower upper : Nat) (regions : graph.PathRegions lower upper) (separated : graph.PathSeparated)
    (aligned : lower%8=0) (beforeBuffer : upper≤buffer.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower) :
    WriteProtection data.child buffer stp pad (SerializerQueries graph inputEnd) := by
  have queryBounds : ∀ query,PathQuery graph query → lower≤query.toNat ∧ query.toNat<upper:=by
    intro query ⟨owner,ownerMember,ownerActive,ownerTag,index,inside,equal⟩
    have span:=paths.span owner ownerMember ownerActive ownerTag
    have bounds:=regions owner ownerMember ownerActive ownerTag
    have number:=byteAddress_toNat (GasBudget.wordAt source.memory (owner+32#64)) index (by have fits:=span.fits; omega)
    rw [equal,AllocatedBytes.aligned_number,number]
    omega
  refine ⟨?_,?_,?_,?_,protection.cacheBefore,protection.stateBefore,protection.padBefore⟩
  · intro query required
    rcases required with field|path
    · exact protection.earlier query field
    · have bounds:=queryBounds query path; omega
  · intro query required
    rcases required with field|path
    · exact protection.stateAway query field
    · have bounds:=queryBounds query path
      exact CopyGeneral.Away.before stp query 200 lower stateBefore (by have small:=query.isLt; omega) bounds.1
  · intro query required
    rcases required with field|path
    · exact protection.padAway query field
    · have bounds:=queryBounds query path
      exact CopyGeneral.Away.before pad query 136 lower padBefore (by have small:=query.isLt; omega) bounds.1
  · intro i inside live query required
    rcases required with field|⟨owner,ownerMember,ownerActive,ownerTag,index,within,equal⟩
    · exact protection.cacheAway i inside live query field
    · rw [equal]
      have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i))
      exact separated owner ownerMember ownerActive ownerTag index within (data.child i) (data.child_member graph member active tag i inside) live 24 (by omega)

/-- A completed writer retains full path contents and layout in the same
reconstructed graph. Its actual footer cache stores cannot alias any path word. -/
theorem FinishOutput.after_paths {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (next : TrieWalk.Graph post.memory post.memaddrs) (same : next.valid=graph.valid)
    (member : graph.valid node) (active : node≠0#64) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (covers : ∀ query,RegisteredField graph query → keep query) (pathCovers : ∀ query,PathQuery graph query → keep query)
    (paths : graph.PathBytes source.be) (pathLower pathUpper : Nat) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated) :
    next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have dataMemory:=output.data_memory graph member active lower upper regions disjoint covers
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    obtain ⟨owner,offset,ownerMember,ownerActive,inside,dataOffset,equal⟩:=required.data_location graph query
    rw [equal]
    exact dataMemory owner offset ownerMember ownerActive inside dataOffset
  have bytesAgree : ∀ owner,graph.valid owner → owner≠0#64 → (GasBudget.wordAt source.memory owner=1#64 ∨ GasBudget.wordAt source.memory owner=2#64) →
      ∀ index<(GasBudget.wordAt source.memory (owner+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (GasBudget.wordAt source.memory (owner+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (GasBudget.wordAt source.memory (owner+32#64)) index)):=by
    intro owner ownerMember ownerActive ownerTag index inside
    have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory node)
    exact output.memory _ (pathCovers _ ⟨owner,ownerMember,ownerActive,ownerTag,index,inside,rfl⟩)
      (separated owner ownerMember ownerActive ownerTag index inside node member active 8 (by omega))
      (separated owner ownerMember ownerActive ownerTag index inside node member active 16 (by omega))
  exact ⟨paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next same output.runtime.1 output.runtime.2.1 agree bytesAgree,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower pathUpper same agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next same agree⟩


/-- Restoring actual caller scopes or transporting an earlier read-only
preparation preserves the completed writer's physical result. -/
theorem FinishOutput.reframe {source post source' post' : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep)
    (entry : Input.LocalEffects.erase source'=Input.LocalEffects.erase source)
    (exitFrame : Input.LocalEffects.erase post'=Input.LocalEffects.erase post) :
    FinishOutput source' post' node buffer bytes keep := by
  have sourceMemory:=Input.LocalEffects.memory_of_erase source source' entry
  have postMemory:=Input.LocalEffects.memory_of_erase post post' exitFrame
  have sourceGlobals:=congrArg PanSemStateFiniteExact.globals entry
  have postGlobals:=congrArg PanSemStateFiniteExact.globals exitFrame
  change source'.globals=source.globals at sourceGlobals
  change post'.globals=post.globals at postGlobals
  have sourceFields:=Input.MemoryMetadata.of_frame entry
  have postFields:=Input.MemoryMetadata.of_frame exitFrame
  have sourceMetadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) sourceFields
  have postMetadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) postFields
  refine ⟨(congrFun postMemory _).trans output.pointerStored,(congrFun postMemory _).trans output.lengthStored,?_,
    ⟨(Input.MemoryMetadata.domain postFields).trans (output.runtime.1.trans (Input.MemoryMetadata.domain sourceFields).symm),
      (Input.MemoryMetadata.endian postFields).trans (output.runtime.2.1.trans (Input.MemoryMetadata.endian sourceFields).symm),
      (Input.MemoryMetadata.code postFields).trans (output.runtime.2.2.trans (Input.MemoryMetadata.code sourceFields).symm)⟩,
    postMetadata.trans (output.metadata.trans sourceMetadata.symm),?_,?_,?_⟩
  · obtain ⟨next,cell,cap,aligned,floor⟩:=output.heap
    exact ⟨next,by rw [postGlobals]; exact cell,cap,aligned,floor⟩
  · intro key different
    rw [postGlobals,sourceGlobals]
    exact output.globals key different
  · intro query required pointerAway lengthAway
    exact (congrFun postMemory query).trans ((output.memory query required pointerAway lengthAway).trans (congrFun sourceMemory query).symm)
  · intro query above
    exact (congrFun postMemory query).trans ((output.scratch query above).trans (congrFun sourceMemory query).symm)

/-- All earlier input backing words survive the actual footer as well as
the child hashes and value write, since the node itself is above that input. -/
theorem FinishOutput.input_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) (inputEnd : Nat)
    (covers : ∀ query,2701134824≤query.toNat → query.toNat<inputEnd → keep query) (nodeFloor : inputEnd≤node.toNat) (nodeBefore : node.toNat+24≤2952790016)
    (query : BitVec 64) (above : 2701134824≤query.toNat) (before : query.toNat<inputEnd) : post.memory query=source.memory query := by
  have pointerNumber : (node+8#64).toNat=node.toNat+8:=byteAddress_toNat node 8 (by omega)
  have lengthNumber : (node+16#64).toNat=node.toNat+16:=byteAddress_toNat node 16 (by omega)
  apply output.memory query (covers query above before)
  · intro same
    rw [same,pointerNumber] at before
    omega
  · intro same
    rw [same,lengthNumber] at before
    omega

/-- Combined actual writer continuation contract for the outer serializer:
same graph, values, path bytes/layout and populated-cache length bound. -/
theorem FinishOutput.after_graph_paths {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (covers : ∀ query,RegisteredField graph query → keep query) (pathCovers : ∀ query,PathQuery graph query → keep query)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop) (values : TrieWalk.Values graph valueLimit property)
    (paths : graph.PathBytes source.be) (pathLower pathUpper : Nat) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (limit : Nat) (bounded : CachedLengths graph limit) (newBound : bytes≤limit) :
    ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (TrieWalk.Values next valueLimit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated ∧ CachedLengths next limit := by
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextCached⟩:=output.after_graph graph member active lower upper regions disjoint covers valueLimit property values limit bounded newBound
  obtain ⟨nextPaths,nextPathRegions,nextSeparated⟩:=output.after_paths graph next same member active lower upper regions disjoint covers pathCovers paths pathLower pathUpper pathRegions separated
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,nextCached⟩


/-- Existing payload ownership derives a real first-byte read when the
single-byte RLP decision needs one; every other length may choose zero. -/
theorem branch_first_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property) :
    ∃ first : BitVec 64,view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word first)) := by
  by_cases one : view.length=1#64
  · have mapped:=view.payload.2.2 0 (by rw [one]; decide)
    simp only [byteAddress,BitVec.add_zero] at mapped
    cases stored : source.memory (panByteAlignHOL (width:=64) view.pointer) with
    | word word=>
      refine ⟨BitVec.ofNat 64 (panGetByteHOL view.pointer word source.be).toNat,?_⟩
      intro _
      simp [eval,evalHOLExact,toExact,panMemLoadByteHOL,stored,mapped]
  · exact ⟨0#64,fun impossible=>(one impossible).elim⟩

def branchAllowance (cacheLimit valueLimit : Nat) : Nat:=
  16*(CurrentKeccak.Hash.boundedBodyPrice cacheLimit+48)+Input.CopyAny.price valueLimit+114

/-- The whole real branch phase, from payload scan through allocation,
all child/value writes and cache return. Every reached writer fact comes
from this same execution's actual preparation and buffer trace. -/
theorem branch_finish_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap stp pad : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt source.memory node=3#64) (lower upper inputEnd : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64) :
    source.clock-(evaluateHOLFiniteState source afterExtension).2.clock≤branchAllowance cacheLimit valueLimit := by
  let data:=ReferenceScanData.of_graph source node graph member active tag lower upper regions environment.domain
  obtain ⟨first,firstRead⟩:=branch_first_read source node valueLimit property view
  let result:=evaluateHOLFiniteState source afterExtension
  have run : evaluateHOLFiniteState source afterExtension=(result.1,result.2):=rfl
  rcases branch_buffer_trace source result.2 node heap valueLimit property view data first firstRead valueFits environment.installed
    nodeCell tagCell payloadCell heapCell heapLower heapUpper result.1 run with stopped|reached
  · unfold branchAllowance
    exact Nat.le_trans stopped (by omega)
  · obtain ⟨current,inner,prepared,payload,header,_trace,frame,exactCount,_payloadBound,output,nodeAfter,tagAfter,forward,prefixPrice,scope,continued⟩:=reached
    have memory:=Input.LocalEffects.memory_of_erase source prepared frame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
    change prepared.memaddrs=source.memaddrs at domain
    let preparedGraph:=TrieWalk.Graph.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph domain (fun query _=>congrFun memory query)
    have same : preparedGraph.valid=graph.valid:=rfl
    have preparedTags : ∀ owner,graph.valid owner → owner≠0#64 → GasBudget.wordAt prepared.memory owner=GasBudget.wordAt source.memory owner:=by
      intro owner _ _
      rw [memory]
    have preparedRegions:=regions.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph lower upper same preparedTags
    have preparedDisjoint:=disjoint.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph same preparedTags
    have preparedTag : GasBudget.wordAt prepared.memory node=3#64:=by rw [memory]; exact tag
    have preparedEnvironment:=environment.of_frame frame
    let preparedData:=data.of_frame frame
    let preparedView:=view.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs node 160#64 168#64 valueLimit domain (congrFun memory _) (congrFun memory _)
    have preparedNode : prepared.locals.lookup (ofString "node")=some (.val (.word node)):=
      (output.locals (ofString "node") (by decide) (by decide) (by decide)).symm.trans nodeAfter
    have protection:=WriteProtection.of_graph preparedData preparedGraph member active preparedTag lower upper inputEnd preparedRegions preparedDisjoint
      preparedEnvironment beforeHeap (Nat.le_trans beforeHeap heapUpper) stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
    have pointerKept : BranchQueries preparedGraph inputEnd (node+160#64):=by
      refine Or.inl ⟨node,160,member,active,?_,by decide,rfl⟩
      rw [preparedTag]; decide
    have lengthKept : BranchQueries preparedGraph inputEnd (node+168#64):=by
      refine Or.inl ⟨node,168,member,active,?_,by decide,rfl⟩
      rw [preparedTag]; decide
    have lengths : ∀ i,i<16 → (preparedData.length i).toNat≤cacheLimit:=
      ReferenceScanData.of_graph_lengths source node graph member active tag lower upper regions environment.domain cacheLimit bounded
    have budget : preparedData.total 16≤payload.toNat:=by
      change data.total 16≤payload.toNat
      omega
    have valueSmall : preparedView.length.toNat+32<2^64:=by
      change view.length.toNat+32<2^64
      have bound:=view.payload.1
      omega
    have writerPrice:=output.writer_cost preparedData (BranchQueries preparedGraph inputEnd) heapAligned heapLower preparedEnvironment preparedNode tagAfter budget protection
      (preparedData.branch_queries preparedGraph member active preparedTag inputEnd) cacheLimit lengths
      (by
        intro i inside live _nonHash _populated
        exact reference_cache_mapped prepared preparedGraph lower upper preparedRegions preparedEnvironment.domain _
          (preparedData.child_member preparedGraph member active preparedTag i inside) live 24 (by decide) (by decide))
      preparedView pointerKept lengthKept valueSmall
    rw [continued] at writerPrice
    change current.clock-inner.clock≤(CurrentKeccak.Hash.boundedBodyPrice cacheLimit+48)*16+Input.CopyAny.price view.length.toNat+21 at writerPrice
    have copyBound : Input.CopyAny.price view.length.toNat≤Input.CopyAny.price valueLimit:=by
      have bound:=view.payload.1
      unfold Input.CopyAny.price
      omega
    have clockEq:=scope.clock
    change result.2.clock=inner.clock at clockEq
    change source.clock-result.2.clock≤branchAllowance cacheLimit valueLimit
    unfold branchAllowance
    omega


/-- Real mapped branch entry words. The three frame mappings are supplied
by the actual prepared48-byte scratch record; only its payload must be zero. -/
structure BranchEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node : BitVec 64) : Prop where
  frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame))
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  headerMapped : source.memaddrs node
  headerStored : source.memory node=.word 3#64
  payloadMapped : source.memaddrs (frame+40#64)
  payloadStored : source.memory (frame+40#64)=.word 0#64
  bufferMapped : source.memaddrs (frame+24#64)
  lengthMapped : source.memaddrs (frame+32#64)

def branchStart (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) :=
  bind (bind (bind (bind source "k" 3#64) "payload" 0#64) "cbuf" (GasBudget.wordAt source.memory (frame+24#64)))
    "clen" (GasBudget.wordAt source.memory (frame+32#64))

theorem entry_field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer offset word : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (mapped : source.memaddrs (pointer+offset)) (stored : source.memory (pointer+offset)=.word word) :
    eval source (entryField name offset)=some (.val (.word word)) := by
  simp [eval,entryField,evalHOLExact,evalListHOLExact,toExact,localVar,cell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem branch_start_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) :
    (branchStart source frame).locals.lookup (ofString "k")=some (.val (.word 3#64)) ∧
      (branchStart source frame).locals.lookup (ofString "payload")=some (.val (.word 0#64)) ∧
      (branchStart source frame).locals.lookup (ofString "node")=source.locals.lookup (ofString "node") := by
  simp [branchStart,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

/-- All four genuine entry declarations read existing mapped words and
reach their actual state without spending a source call/loop tick. -/
theorem BranchEntry.execution {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64}
    (entry : BranchEntry source frame node) : Input.CallPrefix.Execution source entryTrace (branchStart source frame) := by
  let first:=bind source "k" 3#64
  let second:=bind first "payload" 0#64
  let third:=bind second "cbuf" (GasBudget.wordAt source.memory (frame+24#64))
  have firstFrame : first.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other source "k" "fr" 3#64 (by decide)).trans entry.frameCell
  have secondFrame : second.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other first "payload" "fr" 0#64 (by decide)).trans firstFrame
  have thirdFrame : third.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other second "cbuf" "fr" _ (by decide)).trans secondFrame
  have tagRead:=entry_field_read source "node" node 0#64 3#64 entry.nodeCell (by simpa only [BitVec.add_zero] using entry.headerMapped)
    (by simpa only [BitVec.add_zero] using entry.headerStored)
  have payloadRead:=entry_field_read first "fr" frame 40#64 0#64 firstFrame entry.payloadMapped entry.payloadStored
  have bufferRead:=entry_field_read second "fr" frame 24#64 (GasBudget.wordAt source.memory (frame+24#64)) secondFrame entry.bufferMapped
    (reference_word_stored source.memory _)
  have lengthRead:=entry_field_read third "fr" frame 32#64 (GasBudget.wordAt source.memory (frame+32#64)) thirdFrame entry.lengthMapped
    (reference_word_stored source.memory _)
  exact .step (.declare source _ _ _ _ tagRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.step (.declare first _ _ _ _ payloadRead (by simp [shapeOfHOLExact,shapeEqHOL]))
    (.step (.declare second _ _ _ _ bufferRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.step (.declare third _ _ _ _ lengthRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.done _))))

/-- The real branch entry retains outcome, clock and every nonlocal field
while its literal extension test is skipped. This holds on all outcomes. -/
theorem BranchEntry.observe {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64}
    (entry : BranchEntry source frame node) :
    Input.CallPrefix.observe (evaluateHOLFiniteState source body)=
      Input.CallPrefix.observe (evaluateHOLFiniteState (branchStart source frame) afterExtension) := by
  let current:=branchStart source frame
  have tagCell:= (branch_start_cells source frame).1
  have skipped : evaluateHOLFiniteState current extensionChoice=(none,current):=by
    rw [entry_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip,current]
  have actual:=entry.execution.observe afterLength
  rw [←entry_shapes.1,entry_shapes.2.1,evaluateHOLFiniteState_seq_line780,skipped] at actual
  exact actual

/-- The complete unchanged finish body on a real branch entry has the
same all-outcome allowance as its checked branch phase. -/
theorem body_branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap stp pad : BitVec 64)
    (entry : BranchEntry source frame node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤branchAllowance cacheLimit valueLimit := by
  let current:=branchStart source frame
  have cells:=branch_start_cells source frame
  have tag : GasBudget.wordAt current.memory node=3#64:=by simp only [current,branchStart,QueryBranch.bind,setVarHOLFinite,GasBudget.wordAt,entry.headerStored,MemoryBytes.wordBits]
  have price:=branch_finish_cost current node heap stp pad graph member active tag lower upper inputEnd regions disjoint
    (environment.of_frame rfl) heapCell heapLower heapUpper heapAligned beforeHeap stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
    (cells.2.2.trans entry.nodeCell) cells.1 cells.2.1 cacheLimit bounded valueLimit property view valueFits
  have same:=congrArg (fun observed=>observed.1.2) entry.observe
  change (evaluateHOLFiniteState source body).2.clock=(evaluateHOLFiniteState current afterExtension).2.clock at same
  rw [same]
  exact price


/-- The actual preparation/allocation prefix has no escaping caller return.
Its helper calls all resume into their genuine scoped continuations. -/
theorem branch_buffer_safe : Input.LocalPrefix (ofString "node") (Input.CallPrefix.program (.command branchChoice::bufferTrace) .skip) := by
  exact .seq (branch_safe _ (by decide) (by decide) (by decide) (by decide))
    (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"] (by decide)
      (.decCall (ofString "buf") .one (ofString "alloc") allocationArguments (by decide)
        (.seq (.call none (ofString "rlp_encode_list_header") headerArguments (by intro name impossible; cases impossible))
          (.dec (ofString "off") .one (localVar "hl") (by decide) .skip))))

/-- Every actual branch-phase return must have reached its real writer.
Unlike a mere cost disjunction, this keeps its genuine continuation even
when the entry clock lies below the conservative prefix allowance. -/
theorem branch_buffer_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (data : ReferenceScanData source node) (first : BitVec 64)
    (firstRead : view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (fits : limit+546<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    ∃ current inner prepared payload header,
      Input.CallPrefix.Execution source (.command branchChoice::bufferTrace) current ∧ Input.LocalEffects.erase prepared=Input.LocalEffects.erase source ∧
      payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length ∧ payload.toNat≤limit+537 ∧
      BufferOutput prepared current heap payload header ∧ current.locals.lookup (ofString "node")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 3#64)) ∧ source.clock-current.clock≤93 ∧
      Input.CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current writerTail=(some (.returned value),inner) := by
  have shape : afterExtension=Input.CallPrefix.program (.command branchChoice::bufferTrace) writerTail:=by rw [buffer_shape.2,buffer_shape.1]; rfl
  rcases Input.CallPrefix.classify_frame source (.command branchChoice::bufferTrace) with stopped|reached
  · have observed:=congrArg (fun observation=>observation.1.1) (stopped writerTail)
    change (evaluateHOLFiniteState source (Input.CallPrefix.program (.command branchChoice::bufferTrace) writerTail)).1=
      (evaluateHOLFiniteState source (Input.CallPrefix.program (.command branchChoice::bufferTrace) .skip)).1 at observed
    rw [←shape,normal] at observed
    exact ((branch_buffer_safe.summary_full source).2.1 value observed.symm).elim
  · obtain ⟨current,trace⟩:=reached
    let inner:=(evaluateHOLFiniteState current writerTail).2
    have observed:=trace.observe writerTail
    rw [←shape,normal] at observed
    have outcome:=congrArg (fun observation=>observation.1.1) observed
    change some (.returned value)=(evaluateHOLFiniteState current writerTail).1 at outcome
    have price:=branch_buffer_cost source node heap limit property view (by omega) installed nodeCell tagCell payloadCell heapCell heapUpper
    rw [trace.skip_clock] at price
    have clock:=congrArg (fun observation=>observation.1.2) observed
    have fields:=congrArg Prod.snd observed
    change post.clock=inner.clock at clock
    change Input.LocalEffects.erase post=Input.LocalEffects.erase inner at fields
    obtain ⟨prepared,payload,header,frame,exactCount,bound,output,nodeAfter,tagAfter⟩:=branch_buffer_normal source current node heap limit property view data first firstRead
      fits installed nodeCell tagCell payloadCell heapCell heapLower heapUpper trace
    exact ⟨current,inner,prepared,payload,header,trace,frame,exactCount,bound,output,nodeAfter,tagAfter,price,⟨clock,fields⟩,Prod.ext outcome.symm rfl⟩


/-- Full memory agreement and the same registered membership identify all
physical node/input/path queries across actual read-only preparation. -/
theorem serializer_queries_of_memory (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (next : TrieWalk.Graph current.memory current.memaddrs)
    (same : next.valid=graph.valid) (memory : current.memory=source.memory) (inputEnd : Nat) :
    SerializerQueries next inputEnd=SerializerQueries graph inputEnd := by
  funext query
  simp only [SerializerQueries,BranchQueries,RegisteredField,PathQuery,same,memory]

/-- A real byte read is unchanged by actual read-only preparation. -/
theorem byte_read_of_frame (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer first : BitVec 64)
    (frame : Input.LocalEffects.erase current=Input.LocalEffects.erase source)
    (read : eval source (.loadByte (.const pointer))=some (.val (.word first))) :
    eval current (.loadByte (.const pointer))=some (.val (.word first)) := by
  have memory:=Input.LocalEffects.memory_of_erase source current frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change current.memaddrs=source.memaddrs at domain
  change current.be=source.be at endian
  simp only [eval,evalHOLExact,toExact,memory,domain,endian] at read ⊢
  convert read using 1 <;> congr 2 <;> apply Subsingleton.elim

/-- Complete actual normal branch preparation/allocation/writing retains
the serializer's original graph queries and installs a bounded exact cache.
The earlier value-byte extent is a physical input fact, not a future read. -/
theorem branch_finish_normal_band (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap stp pad : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt source.memory node=3#64) (lower upper inputEnd : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64)
    (inputBounds : view.pointer.toNat+view.length.toNat≤inputEnd ∧ (view.length=0#64 ∨ 2701134824≤view.pointer.toNat))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤valueLimit+546 ∧ FinishOutput source post node heap bytes (WithBand (SerializerQueries graph inputEnd) upper heap.toNat) := by
  let data:=ReferenceScanData.of_graph source node graph member active tag lower upper regions environment.domain
  obtain ⟨first,firstRead⟩:=branch_first_read source node valueLimit property view
  obtain ⟨current,inner,prepared,payload,header,_trace,frame,exactCount,payloadBound,output,nodeAfter,tagAfter,_price,scope,continued⟩:=
    branch_buffer_return source post node heap valueLimit property view data first firstRead valueFits environment.installed nodeCell tagCell payloadCell heapCell heapLower heapUpper value normal
  have memory:=Input.LocalEffects.memory_of_erase source prepared frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change prepared.memaddrs=source.memaddrs at domain
  change prepared.be=source.be at endian
  have agree : ∀ query,graph.Footprint query → prepared.memory query=source.memory query:=fun query _=>congrFun memory query
  let preparedGraph:=TrieWalk.Graph.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph domain agree
  have same : preparedGraph.valid=graph.valid:=rfl
  have preparedTags : ∀ owner,graph.valid owner → owner≠0#64 → GasBudget.wordAt prepared.memory owner=GasBudget.wordAt source.memory owner:=by
    intro owner _ _
    rw [memory]
  have preparedRegions:=regions.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph lower upper same preparedTags
  have preparedDisjoint:=disjoint.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph same preparedTags
  have preparedPaths:=paths.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs source.be prepared.be graph preparedGraph same domain endian agree
    (by intro owner ownerMember ownerActive ownerTag index inside; exact congrFun memory _)
  have preparedPathRegions:=pathRegions.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph lower upper same agree
  have preparedSeparated:=separated.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs graph preparedGraph same agree
  have preparedTag : GasBudget.wordAt prepared.memory node=3#64:=by rw [memory]; exact tag
  have preparedEnvironment:=environment.of_frame frame
  let preparedData:=data.of_frame frame
  let preparedView:=view.of_agreement source.memory prepared.memory source.memaddrs prepared.memaddrs node 160#64 168#64 valueLimit domain (congrFun memory _) (congrFun memory _)
  have preparedNode : prepared.locals.lookup (ofString "node")=some (.val (.word node)):=
    (output.locals (ofString "node") (by decide) (by decide) (by decide)).symm.trans nodeAfter
  have branchProtection:=WriteProtection.of_graph preparedData preparedGraph member active preparedTag lower upper inputEnd preparedRegions preparedDisjoint
    preparedEnvironment beforeHeap (Nat.le_trans beforeHeap heapUpper) stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
  have originalProtection:=branchProtection.with_paths preparedData preparedGraph member active preparedTag inputEnd preparedPaths lower upper preparedPathRegions preparedSeparated lowerAligned beforeHeap stateBefore padBefore
  have queries:=serializer_queries_of_memory source prepared graph preparedGraph same memory inputEnd
  rw [queries] at originalProtection
  have ordered : lower≤upper:=by have parent:=preparedRegions node member active; omega
  have protection:=originalProtection.with_band upper (stateBefore.trans ordered) (padBefore.trans ordered) (by
    intro i inside live
    have childMember:=preparedData.child_member preparedGraph member active preparedTag i inside
    have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt prepared.memory (preparedData.child i))
    exact (preparedGraph.region_query_bounds lower upper preparedRegions (preparedData.child i) 24 childMember live (by omega)).2)
  have covers : ∀ query,preparedData.Footprint query → WithBand (SerializerQueries graph inputEnd) upper heap.toNat query:=by
    intro query required
    apply Or.inl
    rw [←queries]
    exact Or.inl (preparedData.branch_queries preparedGraph member active preparedTag inputEnd query required)
  have pointerKept : WithBand (SerializerQueries graph inputEnd) upper heap.toNat (node+160#64):=by
    refine Or.inl (Or.inl (Or.inl ⟨node,160,member,active,?_,by decide,rfl⟩))
    rw [tag]; decide
  have lengthKept : WithBand (SerializerQueries graph inputEnd) upper heap.toNat (node+168#64):=by
    refine Or.inl (Or.inl (Or.inl ⟨node,168,member,active,?_,by decide,rfl⟩))
    rw [tag]; decide
  have byteKept : preparedView.length=1#64 → WithBand (SerializerQueries graph inputEnd) upper heap.toNat (panByteAlignHOL (width:=64) preparedView.pointer):=by
    intro one
    refine Or.inl (Or.inl (Or.inr ?_))
    change 2701134824≤(panByteAlignHOL (width:=64) view.pointer).toNat ∧
      (panByteAlignHOL (width:=64) view.pointer).toNat<inputEnd
    have lengthOne : view.length.toNat=1:=by rw [show view.length=1#64 from one]; rfl
    have pointerLower : 2701134824≤view.pointer.toNat:=inputBounds.2.resolve_left (by
      intro zero
      rw [zero] at lengthOne
      contradiction)
    rw [AllocatedBytes.aligned_number]
    omega
  have firstPrepared : preparedView.length=1#64 → eval prepared (.loadByte (.const preparedView.pointer))=some (.val (.word first)):=by
    intro one
    exact byte_read_of_frame source prepared view.pointer first frame (firstRead one)
  have nodeBefore : node.toNat+24≤2952790016:=by
    have region:=regions node member active
    have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory node)
    omega
  have result:=output.finish_output preparedData (WithBand (SerializerQueries graph inputEnd) upper heap.toNat) heapAligned preparedEnvironment preparedNode tagAfter protection covers
    (by
      intro i inside live _nonHash _populated
      exact reference_cache_mapped prepared preparedGraph lower upper preparedRegions preparedEnvironment.domain _
        (preparedData.child_member preparedGraph member active preparedTag i inside) live 24 (by decide) (by decide))
    preparedView first pointerKept lengthKept byteKept
    (by change view.length.toNat+32<2^64; have bound:=view.payload.1; omega) firstPrepared exactCount
    (reference_cache_mapped prepared preparedGraph lower upper preparedRegions preparedEnvironment.domain node member active 8 (by decide) (by decide))
    (reference_cache_mapped prepared preparedGraph lower upper preparedRegions preparedEnvironment.domain node member active 16 (by decide) (by decide)) nodeBefore value continued
  have finalOutput : FinishOutput source post node heap (header+payload.toNat) (WithBand (SerializerQueries graph inputEnd) upper heap.toNat):=
    result.2.reframe frame.symm scope.metadata
  exact ⟨header+payload.toNat,result.1,by have headerBound:=output.headerUpper; omega,finalOutput⟩


/-- Compatibility projection of the actual stronger persistent-band result. -/
theorem branch_finish_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap stp pad : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt source.memory node=3#64) (lower upper inputEnd : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64)
    (inputBounds : view.pointer.toNat+view.length.toNat≤inputEnd ∧ (view.length=0#64 ∨ 2701134824≤view.pointer.toNat))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤valueLimit+546 ∧ FinishOutput source post node heap bytes (SerializerQueries graph inputEnd) := by
  obtain ⟨bytes,answer,bound,output⟩:=branch_finish_normal_band source post node heap stp pad graph member active tag lower upper inputEnd regions disjoint environment
    paths pathRegions separated lowerAligned heapCell heapLower heapUpper heapAligned beforeHeap stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
    nodeCell tagCell payloadCell cacheLimit bounded valueLimit property view valueFits inputBounds value normal
  exact ⟨bytes,answer,bound,output.weaken_keep (fun _ required=>Or.inl required)⟩


/-- The complete unchanged branch finish body returns its exact bounded
cache and full physical serializer frame, through actual initial reads,
branch selection, scan/allocation/writes and lexical restoration. -/
theorem body_branch_normal_band (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap stp pad : BitVec 64)
    (entry : BranchEntry source frame node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64)
    (inputBounds : view.pointer.toNat+view.length.toNat≤inputEnd ∧ (view.length=0#64 ∨ 2701134824≤view.pointer.toNat))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤valueLimit+546 ∧ FinishOutput source post node heap bytes (WithBand (SerializerQueries graph inputEnd) upper heap.toNat) := by
  let current:=branchStart source frame
  let inner:=(evaluateHOLFiniteState current afterExtension).2
  have cells:=branch_start_cells source frame
  have tag : GasBudget.wordAt current.memory node=3#64:=by
    simp only [current,branchStart,QueryBranch.bind,setVarHOLFinite,GasBudget.wordAt,entry.headerStored,MemoryBytes.wordBits]
  have observed:=entry.observe
  rw [normal] at observed
  have outcome:=congrArg (fun observation=>observation.1.1) observed
  change some (.returned value)=(evaluateHOLFiniteState current afterExtension).1 at outcome
  have run : evaluateHOLFiniteState current afterExtension=(some (.returned value),inner):=Prod.ext outcome.symm rfl
  have scope:=congrArg Prod.snd observed
  change Input.LocalEffects.erase post=Input.LocalEffects.erase inner at scope
  obtain ⟨bytes,answer,bound,output⟩ :=branch_finish_normal_band current inner node heap stp pad graph member active tag lower upper inputEnd regions disjoint
    (environment.of_frame rfl) paths pathRegions separated lowerAligned heapCell heapLower heapUpper heapAligned beforeHeap stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
    (cells.2.2.trans entry.nodeCell) cells.1 cells.2.1 cacheLimit bounded valueLimit property view valueFits inputBounds value run
  exact ⟨bytes,answer,bound,output.reframe rfl scope⟩


/-- Compatibility projection retaining the existing original-query interface. -/
theorem body_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap stp pad : BitVec 64)
    (entry : BranchEntry source frame node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2701131776≤heap.toNat)
    (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0) (beforeHeap : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit)
    (valueLimit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit property) (valueFits : valueLimit+546<2^64)
    (inputBounds : view.pointer.toNat+view.length.toNat≤inputEnd ∧ (view.length=0#64 ∨ 2701134824≤view.pointer.toNat))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤valueLimit+546 ∧ FinishOutput source post node heap bytes (SerializerQueries graph inputEnd) := by
  obtain ⟨bytes,answer,bound,output⟩:=body_branch_normal_band source post frame node heap stp pad entry graph member active lower upper inputEnd regions disjoint
    environment paths pathRegions separated lowerAligned heapCell heapLower heapUpper heapAligned beforeHeap stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
    cacheLimit bounded valueLimit property view valueFits inputBounds value normal
  exact ⟨bytes,answer,bound,output.weaken_keep (fun _ required=>Or.inl required)⟩

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

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.write_model
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_value_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_value_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_value_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteModel.value_view
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteModel.byte_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_loop_value_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_loop_value_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.branch_writes_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.footer_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.footer_execute

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_write_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.writer_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.writer_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.branch_queries
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteProtection.of_graph

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.writer_cost_of_graph

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.finish_output

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.registered_fields_apart
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.after_graph

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.data_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteProtection.with_paths
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.after_paths

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.reframe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.input_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.after_graph_paths

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_first_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_finish_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.entry_field_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_start_cells
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BranchEntry.execution
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BranchEntry.observe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_branch_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_buffer_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_buffer_return

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.serializer_queries_of_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.byte_read_of_frame
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_finish_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_branch_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.bytes_update_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.bytes_update_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WrittenOutput.footer

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.WriteProtection.with_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.weaken_keep

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_finish_normal_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_branch_normal_band

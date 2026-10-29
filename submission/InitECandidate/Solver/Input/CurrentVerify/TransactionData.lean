import InitECandidate.Solver.Input.CurrentRlp.HeaderCall
import InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.CurrentVerify.StateReturnedData
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real transaction pointer/count loads come from the same decoded
payload image retained through state_init. Failed record reads and empty
transactions remain covered by the original scan's all-outcome bound. -/
theorem after_state_init_transaction_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payloadLocal : source.locals.lookup (ofString "pl")=some (.val (.word record)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterStateInit=(outcome,post)) :
    source.clock-post.clock≤12582752 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤12582752 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  let count:=VarList.decodedCount input start size
  let actualArray:=VarList.decodedArray array size
  have localRead : eval source (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,localVar,toExact,payloadLocal]
  have arrayRead : eval source transactionArrayExpression=some (.val (.word actualArray)):=
    Witness.load_word_read source (Scalar.plus (localVar "pl") 32) (record+32#64) actualArray
      (Scalar.plus_read source (localVar "pl") record 32 localRead)
      (AllocatedBytes.word_mapped source record 136 32 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.txs
  let next:=bind source "txs" actualArray
  have nextPayload : next.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other source "txs" "pl" actualArray (by decide)).trans payloadLocal
  have nextLocal : eval next (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,localVar,toExact,nextPayload]
  have countRead : eval next transactionCountExpression=some (.val (.word (BitVec.ofNat 64 count))):=
    Witness.load_word_read next (Scalar.plus (localVar "pl") 40) (record+40#64) (BitVec.ofNat 64 count)
      (Scalar.plus_read next (localVar "pl") record 40 nextLocal)
      (AllocatedBytes.word_mapped next record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.count
  rcases transaction_prefix_trace source post actualArray count (by dsimp [count]; omega) arrayRead countRead outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨current,inner,frame,locals,forward,price,endpoint,continued,scanRun⟩:=reached
    have entrySi : (transactionScanEntry source actualArray count).locals.lookup (ofString "si")=source.locals.lookup (ofString "si"):=
      (bind_lookup_other _ "i" "si" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "si" (BitVec.ofNat 64 count) (by decide)).trans
          (bind_lookup_other source "txs" "si" actualArray (by decide)))
    have entryPayload : (transactionScanEntry source actualArray count).locals.lookup (ofString "pl")=source.locals.lookup (ofString "pl"):=
      (bind_lookup_other _ "i" "pl" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "pl" (BitVec.ofNat 64 count) (by decide)).trans
          (bind_lookup_other source "txs" "pl" actualArray (by decide)))
    have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)):=
      (locals _ (by decide)).trans (entrySi.trans data.siLocal)
    have currentPayload : current.locals.lookup (ofString "pl")=some (.val (.word record)):=
      (locals _ (by decide)).trans (entryPayload.trans payloadLocal)
    let scanEntry:=transactionScanEntry source actualArray count
    have scanRecords : VarList.Records scanEntry input pointer array start size:=
      VarList.Records.of_memory source scanEntry input pointer array start size rfl payload.transactions.records
    have scanCounter : scanEntry.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
    have scanCount : scanEntry.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))):=
      (bind_lookup_other _ "i" "ntx" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
    have scanArray : scanEntry.locals.lookup (ofString "txs")=some (.val (.word actualArray)):=
      (bind_lookup_other _ "i" "txs" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "txs" (BitVec.ofNat 64 count) (by decide)).trans (bind_lookup_same _ _ _))
    have nonempty:=transaction_records_nonempty scanEntry current input pointer array start size data.arena.domain scanRecords scanCounter scanCount scanArray scanRun
    have checked : TransactionsNonempty input:=by
      unfold TransactionsNonempty
      rw [←payload.transactions.startEq,←payload.transactions.sizeEq]
      exact nonempty
    exact Or.inr ⟨current,inner,data.of_frame frame currentSi,currentPayload,forward,by omega,endpoint,continued,checked⟩

/-- Whole real main prefix through transaction scanning: the same actual
payload/header/gas/database/state-init run either stops within its allowance
or reaches payload_header with all decoded input data retained. -/
theorem to_after_transaction_scan {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤3387552531 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤3387552531 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input := by
  rcases to_after_state_init_with_data data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,target,inner,tables,returned,currentData,forward,price,continued,endpoint,physical⟩:=reached
    rcases after_state_init_transaction_trace currentData tables.2.1 outcome continued with stopped|reached
    · change target.clock-inner.clock≤12582752 at stopped
      exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,last,lastData,payloadLocal,scanForward,scanPrice,scanClock,lastRun,checked⟩:=reached
      change current.clock≤target.clock at scanForward
      change target.clock-current.clock≤12582752 at scanPrice
      exact Or.inr ⟨current,last,lastData,payloadLocal,by change current.clock≤source.clock; omega,
        by change source.clock-current.clock≤3387552531; omega,endpoint.trans scanClock,lastRun,checked⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_transaction_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_transaction_scan

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

def payloadHeaderArguments : List (ExpHOL 64):=[localVar "si"]
def payloadHeaderCall : ProgHOL 64:=match afterTransactionScan with | .seq _ rest=>rest | _=>.skip
def afterPayloadHeader : ProgHOL 64:=match payloadHeaderCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def payloadHeaderActions : List CallPrefix.Action:=[.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem payload_header_shape : afterTransactionScan=.seq .skip (CallPrefix.program payloadHeaderActions afterPayloadHeader) := by
  simp only [afterTransactionScan,transactionScanTail,afterTransactionCount,afterTransactionArray,transactionDeclarations,afterStateInit,
    afterCodes,afterNodes,nodeCall,afterHeaders,headerCall,afterPayload,body,Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,↓reduceIte,
    payloadHeaderActions,payloadHeaderCall,afterPayloadHeader,payloadHeaderArguments,CallPrefix.program,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem payload_header_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "payload_header")=some ([(ofString "si",.one)],PayloadHeader.body,.one) := by
  have found:=OriginalCode.indexed code installed 788 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_payload_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

theorem payload_header_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    ∃ callee,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadHeaderArguments=some [.val (.word si)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "payload_header") [.val (.word si)]=some (PayloadHeader.body,callee,.one) ∧
      Data input (callEntryStateHOLFinite source callee) pointer si record gasWord boundary := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadHeaderArguments=some [.val (.word si)]:=by
    simp [payloadHeaderArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.siLocal]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "payload_header") (ofString "si") PayloadHeader.body .one si
    (payload_header_code source.code data.arena.code)
  exact ⟨callee,args,called,data.of_frame rfl cell⟩

theorem payload_header_prefix_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : TransactionsNonempty input) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program payloadHeaderActions .skip)).2.clock≤476485158959 := by
  obtain ⟨callee,args,called,entry⟩:=payload_header_entry data
  exact ClockCost.scoped_current source (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments [.val (.word si)]
    PayloadHeader.body .skip callee .one 476485158958 0 args called (PayloadHeaderBalance.body_cost entry checked) (ClockCost.skip source.code)

/-- Local-free physical header facts now returned to the real main caller,
with its actual hdr/pl bindings and complete earlier decoded input. -/
structure AfterHeader (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header : BitVec 64) (boundary encoded : Nat) : Prop where
  data : Data input current pointer si record gasWord boundary
  headerCell : current.locals.lookup (ofString "hdr")=some (.val (.word header))
  payloadCell : current.locals.lookup (ofString "pl")=some (.val (.word record))
  buffers : PayloadHeaderEntry.HeaderBuffers header
  geometry : HeaderEncoding.Geometry header (headerFrontier header)
  fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts current.memory header field
  optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts current.memory header field
  before : boundary+32≤header.toNat
  heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) current
  transactionsZero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0
  withdrawalsZero : Payload.withdrawalCount input=0
  encodedBound : encoded≤8388608

/-- The same actual normal hdr call supplies the returned header and all
nonlocal fields, then restores caller SI/PL and binds that exact hdr word. -/
theorem payload_header_reached {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (actual : CallPrefix.Reaches source (.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments) current) :
    ∃ header encoded,AfterHeader input current pointer si record gasWord header boundary encoded := by
  obtain ⟨callee,args,called,entry⟩:=payload_header_entry data
  obtain ⟨child,returned,run,endpoint⟩:=actual.scoped_known (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments
    [.val (.word si)] PayloadHeader.body callee .one args called
  obtain ⟨header,finished,encoded,physical,answer,scope⟩:=PayloadHeaderBalance.body_normal entry checked returned run
  have frame : LocalEffects.erase current=LocalEffects.erase finished:=by
    rw [endpoint]
    exact scope.metadata
  have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)):=by
    rw [endpoint]
    simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using data.siLocal
  have currentPayload : current.locals.lookup (ofString "pl")=some (.val (.word record)):=by
    rw [endpoint]
    simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using payload
  have currentHeader : current.locals.lookup (ofString "hdr")=some (.val (.word header)):=by
    rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have retained:=physical.data.of_frame frame currentSi
  have memory:=LocalEffects.memory_of_erase finished current frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change current.globals=finished.globals at globals
  obtain ⟨heap,cell,lower,upper,aligned⟩:=physical.heapAfter
  have heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) current:=⟨heap,by rw [globals]; exact cell,lower,upper,aligned⟩
  have cells (offset : Nat) (inside : offset≤240) : current.memory (HeaderEncoding.address header offset)=finished.memory (HeaderEncoding.address header offset):=congrFun memory _
  exact ⟨header,encoded,retained,currentHeader,currentPayload,physical.buffers,physical.geometry,
    (fun field member=>HeaderEncoding.FieldFacts.of_cells finished.memory current.memory header field cells (physical.fields field member)),
    (fun field member=>HeaderEncoding.FieldFacts.of_cells finished.memory current.memory header field cells (physical.optional field member)),
    physical.before,heapAfter,physical.transactionsZero,physical.withdrawalsZero,physical.sizeBound⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_reached

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Every actual header caller either stops within its allowance or reaches
its original continuation with the same returned physical header. -/
theorem after_transaction_scan_header_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionScan=(outcome,post)) :
    source.clock-post.clock≤476485158959 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤476485158959 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rw [payload_header_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at run
  rcases CallPrefix.priced_frame_trace source post payloadHeaderActions afterPayloadHeader 476485158959
    (payload_header_prefix_cost data checked) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    have actual : CallPrefix.Reaches source (.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments) current:=
      execution.singleton
    obtain ⟨header,encoded,physical⟩:=payload_header_reached data payload checked actual
    exact Or.inr ⟨current,inner,header,encoded,physical,forward,price,endpoint,continued⟩

/-- The complete original run_attempt prefix through the real payload_header
return. This is a source-clock allowance, with all stopped outcomes included. -/
theorem to_after_payload_header {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤479872711490 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤479872711490 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rcases to_after_transaction_scan data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,beforeData,payload,forward,price,endpoint,continued,checked⟩:=reached
    rcases after_transaction_scan_header_trace beforeData payload checked outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,header,encoded,physical,headerForward,headerPrice,scope,rest⟩:=reached
      have scopeClock:=scope.clock
      exact Or.inr ⟨current,inner,header,encoded,physical,by omega,by omega,endpoint.trans scopeClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_transaction_scan_header_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_payload_header

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_header_hash with | .function fn=>progToHOL fn.body | _=>.skip
def afterMark : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterEncode : ProgHOL 64:=match afterMark with | .decCall _ _ _ _ rest=>rest | _=>.skip
def hashArguments : List (ExpHOL 64):=[.rfield 0 (localVar "e"),.rfield 1 (localVar "e"),localVar "out"]
def hashCall : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") hashArguments
def releaseCall : ProgHOL 64:=.call (some (none,none)) (ofString "heap_release") [localVar "mark"]
def returnZero : ProgHOL 64:=.return (.const 0#64)

set_option maxRecDepth 100000 in
theorem shapes : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "e") HeaderEncoding.returnShape (ofString "encode_header") [localVar "h"] afterEncode ∧
    afterEncode=.seq hashCall (.seq releaseCall returnZero) := by
  simp only [body,afterMark,afterEncode,Guest.Software.guestFn_header_hash,progToHOL,expToHOL,shapeToHOL,
    hashCall,hashArguments,releaseCall,returnZero,HeaderEncoding.returnShape,localVar,List.map_cons,List.map_nil,Option.map_none]
  trivial

/-- Only the actual encoded size is needed to price every final hash outcome.
Malformed pointers and failed memory accesses remain included. -/
theorem after_encode_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : BitVec 64) (encoded : Nat)
    (bounded : encoded≤916) (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "e")=some (HeaderEncoding.encodedPair start encoded)) :
    source.clock-(evaluateHOLFiniteState source afterEncode).2.clock≤955 := by
  have sizeRead : eval source (.rfield 1 (localVar "e"))=some (.val (.word (BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,toExact,localVar,cell,HeaderEncoding.encodedPair]
  have called:=CurrentKeccak.Hash.dynamic_call_cost source (.rfield 0 (localVar "e")) (.rfield 1 (localVar "e"))
    (localVar "out") encoded installed (by omega) sizeRead
  have allowance : CurrentKeccak.Hash.bodyPrice encoded+1≤954:=by unfold CurrentKeccak.Hash.bodyPrice; omega
  have first : source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤954:=Nat.le_trans called allowance
  rw [shapes.2.2]
  exact ClockCost.sequence_current source hashCall (.seq releaseCall returnZero) 954 1 first
    (ClockCost.sequence source.code releaseCall returnZero 1 0 (HeapScope.release_call_cost source.code installed (some none) _)
      (ClockCost.returned source.code _))

/-- A real normal header encoder supplies the length used by this same hash.
Its allocator room is derived inside the encoder's all-outcome contract. -/
theorem after_mark_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap : BitVec 64)
    (geometry : HeaderEncoding.Geometry header heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source afterMark).2.clock≤2302 := by
  obtain ⟨callee,called,headerCell⟩:=CurrentRlp.HeaderEncoder.environment source.code.lookup header (CurrentRlp.HeaderEncoder.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "h"]=some [.val (.word header)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,h]
  rw [shapes.2.1]
  apply ClockCost.scoped_reached_current source "e" HeaderEncoding.returnShape (ofString "encode_header") [localVar "h"] _
    CurrentRlp.HeaderEncoder.body afterEncode callee HeaderEncoding.returnShape 1346 955 args called
    (CurrentRlp.HeaderEncoder.body_cost (callEntryStateHOLFinite source callee) header heap geometry domain installed headerCell heapCell heapBound fields optional)
  intro target returned normal checked
  obtain ⟨start,encoded,positive,size,answer,arena,frame,memory⟩:=CurrentRlp.HeaderEncoder.body_normal
    (callEntryStateHOLFinite source callee) target header heap geometry domain installed headerCell heapCell heapBound fields optional returned normal
  have currentInstalled : OriginalCode.Installed (CallNormal.continuationEntry source target "e" returned).code:=
    OriginalCode.after_execution (callEntryStateHOLFinite source callee) target CurrentRlp.HeaderEncoder.body _ normal installed
  have cell : (CallNormal.continuationEntry source target "e" returned).locals.lookup (ofString "e")=some (HeaderEncoding.encodedPair start encoded):=by
    rw [←answer]
    exact CallNormal.continuation_lookup_same _ _ _ _
  exact after_encode_cost _ start encoded size currentInstalled cell

/-- Full original header_hash, including its own mark, encoder, software
Keccak, heap release and return, on every outcome of this physical entry. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap : BitVec 64)
    (geometry : HeaderEncoding.Geometry header heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2303 := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "heap_mark") []=some (HeapScope.markBody,(fun _=>none),.one):=by
    simp [lookupCodeHOLExact,HeapScope.mark_original_code source.code installed]
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  rw [shapes.1]
  apply ClockCost.scoped_reached_current source "mark" .one (ofString "heap_mark") [] [] HeapScope.markBody afterMark callee .one 0 2302
    rfl called (HeapScope.mark_body_cost source.code (callEntryStateHOLFinite source callee) rfl)
  intro target returned normal checked
  rw [HeapScope.mark_shape] at normal
  obtain ⟨read,endpoint⟩:=return_normal (callEntryStateHOLFinite source callee) target HeapScope.heapVar returned normal
  have expected : eval (callEntryStateHOLFinite source callee) HeapScope.heapVar=some (.val (.word heap)):=by
    simp [eval,HeapScope.heapVar,evalHOLExact,toExact,callEntryStateHOLFinite,heapCell]
  have answer : returned=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  have canonical : CallNormal.continuationEntry source target "mark" returned=QueryBranch.bind {source with clock:=source.clock-1} "mark" heap:=by
    rw [endpoint,answer]
    rfl
  have retained : (QueryBranch.bind {source with clock:=source.clock-1} "mark" heap).locals.lookup (ofString "h")=some (.val (.word header)):=
    (bind_lookup_other _ "mark" "h" heap (by decide)).trans h
  have price:=after_mark_cost (QueryBranch.bind {source with clock:=source.clock-1} "mark" heap) header heap geometry domain installed retained heapCell heapBound fields optional
  rw [←canonical] at price
  exact price

end InitECandidate.Solver.Input.CurrentVerify.HeaderHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.after_encode_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual hash/release tail restores its own mark and protects every
older word outside the real output and the fixed Keccak workspaces. -/
theorem after_encode_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (start out heap currentHeap : BitVec 64) (encoded : Nat)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputArena : AllocatedBytes.Arena start encoded) (outArena : AllocatedBytes.Arena out 32)
    (encodedCell : source.locals.lookup (ofString "e")=some (HeaderEncoding.encodedPair start encoded))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word heap)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterEncode=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→ CopyGeneral.Away out query 32→post.memory query=source.memory query := by
  rw [shapes.2.2] at normal
  obtain ⟨hashed,hashRun,remaining⟩:=sequence_returned source post hashCall (.seq releaseCall returnZero) value
    ((LocalPrefix.call (key:=ofString "mark") none _ _ (by simp)).summary_full source).2.1 normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) hashArguments=
      some (CurrentKeccak.Hash.values start out encoded):=by
    simp [hashArguments,HeaderEncoding.encodedPair,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,encodedCell,outCell]
  have globals (key : MlS) : hashed.globals.lookup key=source.globals.lookup key:=by
    have frame:=CurrentKeccak.Hash.call_globals key source.code environment.installed hashArguments source rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState source hashCall).2=GlobalEffects.erase key source at frame
    rw [hashRun] at frame
    exact congrArg Prod.snd frame
  have installed : OriginalCode.Installed hashed.code:=by
    rw [(evaluation_fields source hashed hashCall none hashRun).2.2.2]
    exact environment.installed
  have nextMark : hashed.locals.lookup (ofString "mark")=some (.val (.word heap)):=
    (CallNormal.ignored_lookup source hashed (ofString "mark") (ofString "keccak256") hashArguments hashRun).trans saved
  have nextHeap : hashed.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap)):=(globals _).trans heapCell
  obtain ⟨released,releaseRun,returned⟩:=sequence_returned hashed post releaseCall returnZero value
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
  intro query above outAway
  have stateAway:=CopyGeneral.Away.before 2701132160#64 query 200 2701134824 (by decide) (by decide) above
  have padAway:=CopyGeneral.Away.before 2701132360#64 query 136 2701134824 (by decide) (by decide) above
  have memory:=(CurrentKeccak.Hash.call_frame source hashed 2701132160#64 2701132360#64 start out query encoded environment hashArguments args
    inputArena outArena stateAway padAway outAway hashRun).memory
  rw [postEq,releaseEq]
  exact memory

end InitECandidate.Solver.Input.CurrentVerify.HeaderHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.after_encode_normal

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real encoder return supplies its actual hash input; the following
normal hash/release retains the whole earlier memory and saved heap. -/
theorem after_mark_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap out : BitVec 64)
    (geometry : HeaderEncoding.Geometry header heap)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word heap)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<heap.toNat→CopyGeneral.Away out query 32→post.memory query=source.memory query := by
  obtain ⟨callee,called,headerCell⟩:=CurrentRlp.HeaderEncoder.environment source.code.lookup header (CurrentRlp.HeaderEncoder.original_code source.code environment.installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "h"]=some [.val (.word header)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,h]
  rw [shapes.2.1] at normal
  obtain ⟨funded,child,returned,inner,encoderRun,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source post "e" HeaderEncoding.returnShape
    (ofString "encode_header") [localVar "h"] _ CurrentRlp.HeaderEncoder.body afterEncode callee HeaderEncoding.returnShape args called value normal
  obtain ⟨start,encoded,positive,size,answer,arena,frame,memory⟩:=CurrentRlp.HeaderEncoder.body_normal
    (callEntryStateHOLFinite source callee) child header heap geometry environment.domain environment.installed headerCell heapCell heapBound fields optional returned encoderRun
  let current:=CallNormal.continuationEntry source child "e" returned
  have metadata : MemoryMetadata.erase current=MemoryMetadata.erase (CurrentRlp.HeaderEncoder.heapPost source heap):=frame
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change current.globals=(CurrentRlp.HeaderEncoder.heapPost source heap).globals at globals
  have code:=MemoryMetadata.code metadata
  change current.code=source.code at code
  have domain:=MemoryMetadata.domain metadata
  change current.memaddrs=source.memaddrs at domain
  have ready : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64:=by
    refine ⟨by rw [code]; exact environment.installed,domain.trans environment.domain,?_,?_,environment.stateArena,environment.padArena,
      environment.stateAligned,environment.padAligned⟩
    · rw [globals]
      simpa [CurrentRlp.HeaderEncoder.heapPost,HolFiniteMapExact.update,FUPDATE,ofString] using environment.stateGlobal
    · rw [globals]
      simpa [CurrentRlp.HeaderEncoder.heapPost,HolFiniteMapExact.update,FUPDATE,ofString] using environment.padGlobal
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor heap))):=by
    rw [globals]
    simp [CurrentRlp.HeaderEncoder.heapPost,HolFiniteMapExact.update,FUPDATE]
  have currentEncoded : current.locals.lookup (ofString "e")=some (HeaderEncoding.encodedPair start encoded):=by
    rw [←answer]
    exact CallNormal.continuation_lookup_same _ _ _ _
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=
    (CallNormal.continuation_lookup_other source child "e" "out" returned (by decide)).trans outCell
  have currentMark : current.locals.lookup (ofString "mark")=some (.val (.word heap)):=
    (CallNormal.continuation_lookup_other source child "e" "mark" returned (by decide)).trans saved
  obtain ⟨result,restored,kept,older⟩:=after_encode_normal current inner start out heap (HeaderEncoding.cursor heap) encoded ready arena outArena
    currentEncoded currentOut currentMark currentHeap value remaining
  refine ⟨result,?_,?_,?_⟩
  · rw [endpoint]
    exact restored
  · intro key different
    rw [endpoint]
    exact (kept key different).trans (by
      rw [globals]
      simp [CurrentRlp.HeaderEncoder.heapPost,HolFiniteMapExact.update,FUPDATE,Ne.symm different])
  · intro query above below outAway
    rw [endpoint]
    exact (older query above outAway).trans (memory query below)

end InitECandidate.Solver.Input.CurrentVerify.HeaderHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.after_mark_normal

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete actual header_hash normal return: its own mark is restored and
all older input/header memory outside the output and workspaces survives. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap out : BitVec 64)
    (geometry : HeaderEncoding.Geometry header heap)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out))) (outArena : AllocatedBytes.Arena out 32)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<heap.toNat→CopyGeneral.Away out query 32→post.memory query=source.memory query := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "heap_mark") []=some (HeapScope.markBody,(fun _=>none),.one):=by
    simp [lookupCodeHOLExact,HeapScope.mark_original_code source.code environment.installed]
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  rw [shapes.1] at normal
  obtain ⟨funded,child,returned,inner,markRun,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source post "mark" .one
    (ofString "heap_mark") [] [] HeapScope.markBody afterMark callee .one rfl called value normal
  rw [HeapScope.mark_shape] at markRun
  obtain ⟨read,childEq⟩:=return_normal (callEntryStateHOLFinite source callee) child HeapScope.heapVar returned markRun
  have expected : eval (callEntryStateHOLFinite source callee) HeapScope.heapVar=some (.val (.word heap)):=by
    simp [eval,HeapScope.heapVar,evalHOLExact,toExact,callEntryStateHOLFinite,heapCell]
  have answer : returned=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  let current:=QueryBranch.bind {source with clock:=source.clock-1} "mark" heap
  have canonical : CallNormal.continuationEntry source child "mark" returned=current:=by rw [childEq,answer]; rfl
  rw [canonical] at remaining
  have ready : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64:=environment.of_frame rfl
  have hCell : current.locals.lookup (ofString "h")=some (.val (.word header)):=
    (bind_lookup_other _ "mark" "h" heap (by decide)).trans h
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=
    (bind_lookup_other _ "mark" "out" heap (by decide)).trans outCell
  have saved : current.locals.lookup (ofString "mark")=some (.val (.word heap)):=bind_lookup_same _ _ _
  obtain ⟨result,restored,kept,memory⟩:=after_mark_normal current inner header heap out geometry ready hCell currentOut outArena saved
    heapCell heapBound fields optional value remaining
  rw [endpoint]
  exact ⟨result,restored,kept,memory⟩

end InitECandidate.Solver.Input.CurrentVerify.HeaderHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "header_hash")=some ([(ofString "h",.one),(ofString "out",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 211 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_header_hash) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_header_hash,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- Ordinary header-hash callers add one source tick to the complete body;
all callee entry facts come from the actual two-word signature. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap out : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word header),.val (.word out)])
    (geometry : HeaderEncoding.Geometry header heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "header_hash") arguments)).2.clock≤2304 := by
  obtain ⟨callee,called,h,outCell⟩:=word_pair_environment source.code.lookup (ofString "header_hash") (ofString "h") (ofString "out")
    body .one header out (by decide) (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "header_hash") arguments [.val (.word header),.val (.word out)] body callee .one 2303 args called
    (body_cost (callEntryStateHOLFinite source callee) header heap geometry domain installed h heapCell heapBound fields optional)

/-- The actual ordinary caller retains the helper's genuine heap restoration
and protected memory through its real returned scalar and caller locals. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (header heap out : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word header),.val (.word out)])
    (geometry : HeaderEncoding.Geometry header heap)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (outArena : AllocatedBytes.Arena out 32)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapBound : heap.toNat≤2952790016)
    (fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "header_hash") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ HeapGlobals source post ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<heap.toNat→CopyGeneral.Away out query 32→post.memory query=source.memory query := by
  obtain ⟨callee,called,h,outCell⟩:=word_pair_environment source.code.lookup (ofString "header_hash") (ofString "h") (ofString "out")
    body .one header out (by decide) (original_code source.code environment.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fieldsFrame⟩:=
    CallNormal.ignored_data source post (ofString "header_hash") arguments normal
  have valuesEq : actualValues=[.val (.word header),.val (.word out)]:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨answer,restored,globals,memory⟩:=body_normal (callEntryStateHOLFinite source callee) target header heap out geometry (environment.of_frame rfl)
    h outCell outArena heapCell heapBound fields optional returned bodyRun
  rw [endpoint]
  exact ⟨restored,globals,memory⟩

end InitECandidate.Solver.Input.CurrentVerify.HeaderHash

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderHash.call_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry

def blockHashArguments : List (ExpHOL 64):=[localVar "hdr",localVar "bh"]
def blockHashCall : ProgHOL 64:=.call (some (none,none)) (ofString "header_hash") blockHashArguments
def blockHashAllocation : ProgHOL 64:=match afterPayloadHeader with | .seq _ rest=>rest | _=>.skip
def afterBlockHashAllocation : ProgHOL 64:=match blockHashAllocation with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterBlockHash : ProgHOL 64:=match afterBlockHashAllocation with | .seq _ rest=>rest | _=>.skip
def blockHashActions : List CallPrefix.Action:=[.scoped (ofString "bh") .one (ofString "alloc") [.const 32#64],.command blockHashCall]

def blockHashState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "bh" heap

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem block_hash_shape : afterPayloadHeader=.seq .skip (CallPrefix.program blockHashActions afterBlockHash) := by
  simp only [afterPayloadHeader,payloadHeaderCall,afterTransactionScan,transactionScanTail,afterTransactionCount,afterTransactionArray,
    transactionDeclarations,afterStateInit,afterCodes,afterNodes,nodeCall,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    CallPrefix.cut,↓reduceIte,blockHashActions,blockHashAllocation,afterBlockHashAllocation,afterBlockHash,CallPrefix.program,
    blockHashCall,blockHashArguments,localVar]
  trivial

/-- The real advanced allocator cursor supplies header-encoder geometry;
readable ordinary memory alone is not used to assume allocation funding. -/
theorem AfterHeader.geometry_at {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded) (heap : BitVec 64)
    (afterHeader : (headerFrontier header).toNat≤heap.toNat) (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) :
    HeaderEncoding.Geometry header heap:=
  ⟨physical.geometry.headerLower,physical.geometry.headerAligned,by have before:=physical.geometry.headerBefore; omega,aligned,by omega⟩

/-- The normal allocator callback derives its own room and exact caller
state before invoking the existing physical header-hash contract. -/
theorem block_hash_prefix_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program blockHashActions .skip)).2.clock≤2306 := by
  obtain ⟨heap,heapCell,lower,bounded,aligned⟩:=physical.heapAfter
  obtain ⟨callee,called,amount⟩:=PersistentAlloc.environment source.code.lookup 32#64 (PersistentAlloc.original_code source.code physical.data.arena.code)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "bh") .one (ofString "alloc") [.const 32#64] (.seq blockHashCall .skip))).2.clock≤2306
  apply ClockCost.scoped_reached_current source "bh" .one (ofString "alloc") [.const 32#64] _ PersistentAlloc.body (.seq blockHashCall .skip)
    callee .one 1 2304 rfl called (PersistentAlloc.body_price source.code physical.data.arena.code (callEntryStateHOLFinite source callee) rfl)
  intro child returned normal checked
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child heap 32#64 amount heapCell bounded
    (Trap.original_code source.code physical.data.arena.code) returned normal
  have canonical : CallNormal.continuationEntry source child "bh" returned=blockHashState source heap:=by
    rw [answer]
    have observed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString "bh") (.val (.word heap)) {state with locals:=source.locals}) frame
    simpa only [CallNormal.continuationEntry,emptyLocalsHOLFinite,callEntryStateHOLFinite,blockHashState,QueryBranch.bind,PersistentAlloc.post] using observed
  let current:=blockHashState source heap
  have guards:=PersistentAlloc.guards heap 32#64 room
  have currentHeader : current.locals.lookup (ofString "hdr")=some (.val (.word header)):=
    (bind_lookup_other _ "bh" "hdr" heap (by decide)).trans physical.headerCell
  have currentBh : current.locals.lookup (ofString "bh")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) blockHashArguments=some [.val (.word header),.val (.word heap)]:=by
    simp [blockHashArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentHeader,currentBh]
  have nextHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
    simp [current,blockHashState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have geometry:=physical.geometry_at (PersistentAlloc.rounded heap 32#64) (by omega) guards.2.2.2.1 guards.2.2.2.2
  have first:=HeaderHash.call_cost current header (PersistentAlloc.rounded heap 32#64) heap blockHashArguments args geometry
    physical.data.arena.domain physical.data.arena.code nextHeap guards.2.2.2.1 physical.fields physical.optional
  have price:=ClockCost.sequence_current current blockHashCall .skip 2304 0 first (ClockCost.skip current.code)
  change CallNormal.continuationEntry source child "bh" returned=current at canonical
  rw [←canonical] at price
  exact price

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_hash_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.AfterHeader.geometry_at
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_hash_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry

/-- Real main allocation and header hashing preserve the decoded input and
all prior header facts. Allocation funding comes from this same execution. -/
theorem block_hash_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (execution : CallPrefix.Execution source blockHashActions post) :
    AfterHeader input post pointer si record gasWord header boundary encoded := by
  obtain ⟨heap,heapCell,lower,bounded,aligned⟩:=physical.heapAfter
  have expanded : CallPrefix.Execution source
      (.scoped (ofString "bh") .one (ofString "alloc") [.const 32#64]::[.command blockHashCall]) post:=execution
  obtain ⟨room,remaining⟩:=expanded.alloc_next (ofString "bh") [.const 32#64] heap 32#64 [.command blockHashCall]
    physical.data.arena.code rfl heapCell bounded
  change CallPrefix.Execution (blockHashState source heap) [.command blockHashCall] post at remaining
  have run : evaluateHOLFiniteState (blockHashState source heap) blockHashCall=(none,post):=by
    have actual:=remaining.singleton
    cases actual with | command _ _ run=>exact run
  let current:=blockHashState source heap
  have currentHeader : current.locals.lookup (ofString "hdr")=some (.val (.word header)):=
    (bind_lookup_other _ "bh" "hdr" heap (by decide)).trans physical.headerCell
  have currentBh : current.locals.lookup (ofString "bh")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) blockHashArguments=some [.val (.word header),.val (.word heap)]:=by
    simp [blockHashArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentHeader,currentBh]
  have guards:=PersistentAlloc.guards heap 32#64 room
  have nextHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
    simp [current,blockHashState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have allocationGlobals : HeapGlobals source current:=by
    intro key different
    simp [current,blockHashState,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have environment : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64:=
    ⟨physical.data.keccak.installed,physical.data.keccak.domain,
      (allocationGlobals _ (by decide)).trans physical.data.keccak.stateGlobal,(allocationGlobals _ (by decide)).trans physical.data.keccak.padGlobal,
      physical.data.keccak.stateArena,physical.data.keccak.padArena,physical.data.keccak.stateAligned,physical.data.keccak.padAligned⟩
  have outArena : AllocatedBytes.Arena heap 32:=⟨by have before:=physical.geometry.headerBefore; have lower:=physical.geometry.headerLower; omega,by omega⟩
  have geometry:=physical.geometry_at (PersistentAlloc.rounded heap 32#64) (by omega) guards.2.2.2.1 guards.2.2.2.2
  obtain ⟨restored,hashGlobals,memory⟩:=HeaderHash.call_normal current post header (PersistentAlloc.rounded heap 32#64) heap blockHashArguments args geometry
    environment outArena nextHeap guards.2.2.2.1 physical.fields physical.optional run
  have globals : HeapGlobals source post:=by intro key different; exact (hashGlobals key different).trans (allocationGlobals key different)
  have older (query : BitVec 64) (above : 2701134824≤query.toNat) (below : query.toNat<heap.toNat) : post.memory query=source.memory query:=
    memory query above (by omega) (outArena.away_below heap query 32 aligned below)
  have saved (name : String) : post.locals.lookup (ofString name)=current.locals.lookup (ofString name):=
    CallNormal.ignored_lookup current post (ofString name) (ofString "header_hash") blockHashArguments run
  have siCell : post.locals.lookup (ofString "si")=some (.val (.word si)):=
    (saved "si").trans ((bind_lookup_other _ "bh" "si" heap (by decide)).trans physical.data.siLocal)
  have hdrCell : post.locals.lookup (ofString "hdr")=some (.val (.word header)):=(saved "hdr").trans currentHeader
  have plCell : post.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (saved "pl").trans ((bind_lookup_other _ "bh" "pl" heap (by decide)).trans physical.payloadCell)
  have heapAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) post:=
    ⟨PersistentAlloc.rounded heap 32#64,restored,by omega,guards.2.2.2.1,guards.2.2.2.2⟩
  have heapData : NormalHeapEffects.AtLeast (boundary+32) post:=
    ⟨PersistentAlloc.rounded heap 32#64,restored,by have before:=physical.before; have head:=physical.geometry.headerBefore; omega,
      guards.2.2.2.1,guards.2.2.2.2⟩
  have fields:=evaluation_fields current post blockHashCall none run
  have data : Data input post pointer si record gasWord boundary:=physical.data.of_heap_frame fields.1 fields.2.1 fields.2.2.2 globals heapData siCell (by
    intro query above below
    exact older query above (by have before:=physical.before; have head:=physical.geometry.headerBefore; omega))
  have cells (offset : Nat) (inside : offset≤240) : post.memory (HeaderEncoding.address header offset)=source.memory (HeaderEncoding.address header offset):=by
    have number:=physical.geometry.header_address header (headerFrontier header) offset inside
    apply older
    · rw [number]
      have before:=physical.before
      have inputLower:=physical.data.recordInside
      omega
    · rw [number]
      have before:=physical.geometry.headerBefore
      omega
  exact {physical with
    data:=data,headerCell:=hdrCell,payloadCell:=plCell,heapAfter:=heapAfter,
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory post.memory header field cells (physical.fields field member),
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory post.memory header field cells (physical.optional field member)}

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_hash_reached

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original main hash prefix stops or reaches its literal comparison
continuation with the same retained decoded inputs and header facts. -/
theorem after_header_hash_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterPayloadHeader=(outcome,post)) :
    source.clock-post.clock≤2306 ∨ ∃ current inner,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤2306 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterBlockHash=(outcome,inner) := by
  rw [block_hash_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at run
  rcases CallPrefix.priced_frame_trace source post blockHashActions afterBlockHash 2306 (block_hash_prefix_cost physical) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    exact Or.inr ⟨current,inner,block_hash_reached physical execution,forward,price,endpoint,continued⟩

/-- Complete current main prefix through payload_header and header_hash.
This includes all actual rejected/trapped/timed-out prefixes. -/
theorem to_after_block_hash {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤479872713796 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤479872713796 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterBlockHash=(outcome,inner) := by
  rcases to_after_payload_header data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,header,encoded,physical,forward,price,endpoint,continued⟩:=reached
    rcases after_header_hash_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,retained,hashForward,hashPrice,scope,rest⟩:=reached
      have scopeClock:=scope.clock
      exact Or.inr ⟨current,inner,header,encoded,retained,by omega,by omega,endpoint.trans scopeClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_header_hash_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_block_hash

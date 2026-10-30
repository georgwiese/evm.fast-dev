import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.MutableTable.MemeqVariableCost
import InitECandidate.Solver.Input.MemeqReadOnly
import InitECandidate.Solver.Input.CurrentRlp.HeaderCall
import InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.CurrentVerify.StateReturnedData
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.Input.HeapMarkPrefix
import InitECandidate.Solver.Input.CallPrefixAllocation

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

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Reuse completed physical header facts across actual read-only checks,
with only their real caller bindings supplied separately. -/
theorem AfterHeader.of_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (frame : LocalEffects.erase target=LocalEffects.erase source)
    (siCell : target.locals.lookup (ofString "si")=some (.val (.word si)))
    (hdrCell : target.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (plCell : target.locals.lookup (ofString "pl")=some (.val (.word record))) :
    AfterHeader input target pointer si record gasWord header boundary encoded := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  obtain ⟨heap,cell,lower,upper,aligned⟩:=physical.heapAfter
  have heapAfter : NormalHeapEffects.AtLeast ((PayloadHeaderEntry.headerFrontier header).toNat+16) target:=
    ⟨heap,by rw [globals]; exact cell,lower,upper,aligned⟩
  have cells (offset : Nat) (inside : offset≤240) : target.memory (HeaderEncoding.address header offset)=source.memory (HeaderEncoding.address header offset):=congrFun memory _
  exact {physical with
    data:=physical.data.of_frame frame siCell,headerCell:=hdrCell,payloadCell:=plCell,heapAfter:=heapAfter,
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.fields field member),
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells source.memory target.memory header field cells (physical.optional field member)}

def blockCompareRight : ExpHOL 64:=.op .add [.load .one (.op .add [localVar "pl",.const 0#64]),.const 472#64]
def blockCompareArguments : List (ExpHOL 64):=[localVar "bh",blockCompareRight,.const 32#64]
def blockCompareGuard : ProgHOL 64:=.ite (.cmp .equal (localVar "eq") (.const 0#64)) (.raise (ofString "BlockErr") (.const 5#64)) .skip
def afterBlockCompareResult : ProgHOL 64:=match afterBlockHash with | .decCall _ _ _ _ rest=>rest | _=>.skip
def beforeVersionedHashes : ProgHOL 64:=match afterBlockCompareResult with | .seq _ (.seq _ rest)=>rest | _=>.skip
def blockCompareActions : List CallPrefix.Action:=[.scoped (ofString "eq") .one (ofString "memeq") blockCompareArguments,
  .command blockCompareGuard,.command .skip]

set_option maxRecDepth 100000 in
theorem block_compare_shape : afterBlockHash=CallPrefix.program blockCompareActions beforeVersionedHashes:=by
  simp only [afterPayloadHeader,payloadHeaderCall,afterTransactionScan,transactionScanTail,afterTransactionCount,afterTransactionArray,
    transactionDeclarations,afterStateInit,afterCodes,afterNodes,nodeCall,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    CallPrefix.cut,↓reduceIte,blockHashAllocation,afterBlockHashAllocation,afterBlockHash,CallPrefix.program,
    blockCompareActions,blockCompareArguments,blockCompareRight,blockCompareGuard,afterBlockCompareResult,beforeVersionedHashes,localVar]
  trivial

theorem block_compare_guard_pure : PureDecision blockCompareGuard:=.ite _ (.raised _ _) .skip

/-- The existing all-outcome comparison allowance also covers malformed
operand reads. Its following literal guard and skip consume no source ticks. -/
theorem block_compare_prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program blockCompareActions .skip)).2.clock≤129 := by
  exact MutableTable.MemeqAny.scoped_cost source (localVar "bh") blockCompareRight (ofString "eq") (.seq blockCompareGuard (.seq .skip .skip))
    (MutableTable.MemeqAny.original_code source.code installed)
    (ClockCost.sequence source.code blockCompareGuard (.seq .skip .skip) 0 0
      (ClockCost.conditional source.code _ _ _ 0 0 (ClockCost.raised source.code _ _) (ClockCost.skip source.code))
      (ClockCost.sequence source.code .skip .skip 0 0 (ClockCost.skip source.code) (ClockCost.skip source.code)))

theorem block_compare_prefix_frame (code) (installed : OriginalCode.Installed code) :
    LocalEffects.Preserves code (CallPrefix.program blockCompareActions .skip) := by
  apply LocalEffects.scoped_body code _ _ _ _ _ Memeq32.formals Memeq32.body .one
    (MutableTable.MemeqAny.original_code code installed) (MutableTable.MemeqAny.readonly code)
  exact LocalEffects.sequence code blockCompareGuard (.seq .skip .skip)
    (LocalEffects.conditional code _ _ _ (LocalEffects.raised code _ _) (LocalEffects.skip code))
    (LocalEffects.sequence code .skip .skip (LocalEffects.skip code) (LocalEffects.skip code))

/-- Every actually reached comparison prefix keeps the physical main model.
Its tested result and raised exceptions come from that same execution. -/
theorem block_compare_reached {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (execution : CallPrefix.Execution source blockCompareActions target) :
    AfterHeader input target pointer si record gasWord header boundary encoded := by
  have observed:=execution.erase .skip
  rw [evaluateHOLFiniteState_skip] at observed
  have retained:=block_compare_prefix_frame source.code physical.data.arena.code source rfl
  have frame : LocalEffects.erase target=LocalEffects.erase source:=observed.symm.trans retained
  have saved (key : MlS) (different : key≠ofString "eq") : target.locals.lookup key=source.locals.lookup key:=by
    apply execution.keeps_local key
    intro action member
    simp [blockCompareActions] at member
    rcases member with rfl|rfl|rfl
    · exact CallPrefix.KeepsLocal.scoped key (ofString "eq") .one (ofString "memeq") blockCompareArguments different
    · exact CallPrefix.KeepsLocal.decision key blockCompareGuard block_compare_guard_pure
    · exact CallPrefix.KeepsLocal.decision key .skip .skip
  exact physical.of_frame frame ((saved _ (by decide)).trans physical.data.siLocal)
    ((saved _ (by decide)).trans physical.headerCell) ((saved _ (by decide)).trans physical.payloadCell)

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.AfterHeader.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_compare_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_compare_guard_pure
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_compare_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_compare_prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.block_compare_reached

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual block-hash comparison and BlockErr5 guard either stop or
reach the original version check with all main/header facts retained. -/
theorem after_block_hash_compare_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterBlockHash=(outcome,post)) :
    source.clock-post.clock≤129 ∨ ∃ current inner,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤129 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeVersionedHashes=(outcome,inner) := by
  rw [block_compare_shape] at run
  rcases CallPrefix.priced_frame_trace source post blockCompareActions beforeVersionedHashes 129
    (block_compare_prefix_cost source physical.data.arena.code) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    exact Or.inr ⟨current,inner,block_compare_reached physical execution,forward,price,endpoint,continued⟩

/-- Whole original run_attempt prefix through the actual header-hash
comparison; the next code is the literal is_valid_versioned_hashes caller. -/
theorem to_before_versioned_hashes {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤479872713925 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤479872713925 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeVersionedHashes=(outcome,inner) := by
  rcases to_after_block_hash data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,header,encoded,physical,forward,price,endpoint,continued⟩:=reached
    rcases after_block_hash_compare_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,retained,compareForward,comparePrice,scope,rest⟩:=reached
      have scopeClock:=scope.clock
      exact Or.inr ⟨current,inner,header,encoded,retained,by omega,by omega,endpoint.trans scopeClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_block_hash_compare_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_before_versioned_hashes

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashes
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_is_valid_versioned_hashes with | .function fn=>progToHOL fn.body | _=>.skip
def afterPayload : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterArray : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def afterCount : ProgHOL 64:=match afterArray with | .dec _ _ _ rest=>rest | _=>.skip
def afterVersionArray : ProgHOL 64:=match afterCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterVersionCount : ProgHOL 64:=match afterVersionArray with | .dec _ _ _ rest=>rest | _=>.skip
def afterK : ProgHOL 64:=match afterVersionCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterI : ProgHOL 64:=match afterK with | .dec _ _ _ rest=>rest | _=>.skip
def loopBody : ProgHOL 64:=match afterI with | .seq (.while _ first) _=>first | _=>.skip
def tail : ProgHOL 64:=match afterI with | .seq _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .less (localVar "i") (localVar "ntx")

theorem shapes : body=.dec (ofString "pl") .one (.load .one (Scalar.plus (localVar "si") 0)) afterPayload ∧
    afterPayload=.dec (ofString "txs") .one (.load .one (Scalar.plus (localVar "pl") 32)) afterArray ∧
    afterArray=.dec (ofString "ntx") .one (.load .one (Scalar.plus (localVar "pl") 40)) afterCount ∧
    afterCount=.dec (ofString "vh") .one (.load .one (Scalar.plus (localVar "si") 8)) afterVersionArray ∧
    afterVersionArray=.dec (ofString "nvh") .one (.load .one (Scalar.plus (localVar "si") 16)) afterVersionCount ∧
    afterVersionCount=.dec (ofString "k") .one (.const 0#64) afterK ∧
    afterK=.dec (ofString "i") .one (.const 0#64) afterI ∧
    afterI=.seq (.while test loopBody) tail := by
  simp only [body,afterPayload,afterArray,afterCount,afterVersionArray,afterVersionCount,afterK,afterI,loopBody,tail,test,
    Guest.Software.guestFn_is_valid_versioned_hashes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,Scalar.plus,localVar]
  trivial

theorem tail_shape : tail=.seq (.ite (.cmp .notEqual (localVar "k") (localVar "nvh")) (.return (.const 0#64)) .skip) (.return (.const 1#64)) := by
  simp only [body,afterPayload,afterArray,afterCount,afterVersionArray,afterVersionCount,afterK,afterI,tail,
    Guest.Software.guestFn_is_valid_versioned_hashes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]

/-- A reached scalar/tuple declaration lifts a state observation through its
real lexical restoration. Failed reads and shape checks retain the source. -/
theorem declared_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (shape : ShapeHOL)
    (expression : ExpHOL 64) (rest : ProgHOL 64)
    (observed : ∀ value,eval source expression=some value→shapeEqHOL shape (shapeOfHOLExact value)=true→
      CallPrefix.ScopeFrame (evaluateHOLFiniteState (setVarHOLFinite name value source) rest).2 (setVarHOLFinite name value source)) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source (.dec name shape expression rest)).2 source := by
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · exact ⟨rfl,rfl⟩
  · rename_i value read
    split
    · have actual:=observed value read (by assumption)
      exact ⟨actual.clock,actual.metadata⟩
    · exact ⟨rfl,rfl⟩

theorem declared_word_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (rest : ProgHOL 64)
    (read : eval source expression=some (.val (.word word)))
    (observed : CallPrefix.ScopeFrame (evaluateHOLFiniteState (QueryBranch.bind source name word) rest).2 (QueryBranch.bind source name word)) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source (.dec (ofString name) .one expression rest)).2 source := by
  apply declared_frame source (ofString name) .one expression rest
  intro value actual checked
  have same : value=.val (.word word):=Option.some.inj (actual.symm.trans read)
  subst value
  exact observed

/-- The exact reached zero count makes the original signed loop test false;
none of the transaction-decoding/hash-comparison calls can run. -/
theorem after_i_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source afterI).2 source := by
  have read : eval source test=some (.val (.word 0#64)):=by
    simp [eval,test,evalHOLExact,toExact,localVar,counter,count,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
  have stopped : evaluateHOLFiniteState source (.while test loopBody)=(none,source):=by
    rw [evaluateHOLFiniteState_while_total]
    change evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word 0#64)) at read
    rw [read]
    rfl
  rw [shapes.2.2.2.2.2.2.2,evaluateHOLFiniteState_seq_line780,stopped]
  have quiet : QuietClock.Preserves source.code tail:=by
    rw [tail_shape]
    exact QuietClock.sequence source.code _ _ (QuietClock.conditional source.code _ _ _ (QuietClock.returned source.code _) (QuietClock.skip source.code))
      (QuietClock.returned source.code _)
  have retained : LocalEffects.Preserves source.code tail:=by
    rw [tail_shape]
    exact LocalEffects.sequence source.code _ _ (LocalEffects.conditional source.code _ _ _ (LocalEffects.returned source.code _) (LocalEffects.skip source.code))
      (LocalEffects.returned source.code _)
  exact ⟨quiet source rfl,retained source rfl⟩

theorem after_k_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source afterK).2 source := by
  rw [shapes.2.2.2.2.2.2.1]
  exact declared_word_frame source "i" (.const 0#64) 0#64 afterI rfl
    (after_i_frame _ (bind_lookup_same _ _ _) ((bind_lookup_other source "i" "ntx" 0#64 (by decide)).trans count))

theorem after_version_count_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source afterVersionCount).2 source := by
  rw [shapes.2.2.2.2.2.1]
  exact declared_word_frame source "k" (.const 0#64) 0#64 afterK rfl
    (after_k_frame _ ((bind_lookup_other source "k" "ntx" 0#64 (by decide)).trans count))

theorem after_version_array_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source afterVersionArray).2 source := by
  rw [shapes.2.2.2.2.1]
  apply declared_frame source (ofString "nvh") .one _ afterVersionCount
  intro value read checked
  apply after_version_count_frame
  simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nvh"≠ofString "ntx" from by decide] using count

theorem after_count_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source afterCount).2 source := by
  rw [shapes.2.2.2.1]
  apply declared_frame source (ofString "vh") .one _ afterVersionArray
  intro value read checked
  apply after_version_array_frame
  simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "vh"≠ofString "ntx" from by decide] using count

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashes

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.tail_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.declared_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.declared_word_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.after_i_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.after_k_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.after_version_count_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.after_version_array_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.after_count_frame

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete actual version-check body at the zero transaction count already
derived by the original tries. All setup failures retain the same observation. -/
theorem body_frame {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (zero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0) :
    CallPrefix.ScopeFrame (evaluateHOLFiniteState source body).2 source := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  have countZero : VarList.decodedCount input start size=0:=by
    rw [payload.transactions.startEq,payload.transactions.sizeEq]
    exact zero
  let txs:=VarList.decodedArray array size
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by simp [eval,evalHOLExact,toExact,localVar,data.siLocal]
  have payloadRead : eval source (.load .one (Scalar.plus (localVar "si") 0))=some (.val (.word record)):=
    Witness.load_word_read source _ (si+0#64) record (Scalar.plus_read source (localVar "si") si 0 siRead)
      (AllocatedBytes.word_mapped source si 96 0 data.arena.domain data.siArena (by decide) data.siAligned (by decide))
      (by simpa using data.payloadCell)
  let plState:=QueryBranch.bind source "pl" record
  have plRead : eval plState (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,localVar,plState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have arrayRead : eval plState (.load .one (Scalar.plus (localVar "pl") 32))=some (.val (.word txs)):=
    Witness.load_word_read plState _ (record+32#64) txs (Scalar.plus_read plState (localVar "pl") record 32 plRead)
      (AllocatedBytes.word_mapped plState record 136 32 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.txs
  let arrayState:=QueryBranch.bind plState "txs" txs
  have nextPl : arrayState.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other plState "txs" "pl" txs (by decide)).trans (bind_lookup_same _ _ _)
  have nextRead : eval arrayState (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,toExact,localVar,nextPl]
  have countRead : eval arrayState (.load .one (Scalar.plus (localVar "pl") 40))=some (.val (.word 0#64)):=
    Witness.load_word_read arrayState _ (record+40#64) 0#64 (Scalar.plus_read arrayState (localVar "pl") record 40 nextRead)
      (AllocatedBytes.word_mapped arrayState record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide))
      (by have cell:=payload.transactions.count; rw [countZero] at cell; exact cell)
  rw [shapes.1]
  apply declared_word_frame source "pl" _ record afterPayload payloadRead
  change CallPrefix.ScopeFrame (evaluateHOLFiniteState plState afterPayload).2 plState
  rw [shapes.2.1]
  apply declared_word_frame plState "txs" _ txs afterArray arrayRead
  change CallPrefix.ScopeFrame (evaluateHOLFiniteState arrayState afterArray).2 arrayState
  rw [shapes.2.2.1]
  exact declared_word_frame arrayState "ntx" _ 0#64 afterCount countRead (after_count_frame _ (bind_lookup_same _ _ _))

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "is_valid_versioned_hashes")=some ([(ofString "si",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 792 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_is_valid_versioned_hashes) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_is_valid_versioned_hashes,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The real reached zero-count version checker spends no source clocks;
its straight-line target instructions still need the global target accounting. -/
theorem body_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (zero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤0 := by
  rw [(body_frame data zero).clock]
  omega

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashes

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.body_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashes.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def versionedHashesArguments : List (ExpHOL 64):=[localVar "si"]
def versionedHashesGuard : ProgHOL 64:=.ite (.cmp .equal (localVar "vvh") (.const 0#64)) (.raise (ofString "BlockErr") (.const 6#64)) .skip
def versionedHashesContinuation : ProgHOL 64:=match beforeVersionedHashes with | .decCall _ _ _ _ rest=>rest | _=>.skip
def beforeValidateHeader : ProgHOL 64:=match versionedHashesContinuation with | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip
def versionedHashesActions : List CallPrefix.Action:=[.scoped (ofString "vvh") .one (ofString "is_valid_versioned_hashes") versionedHashesArguments,
  .command .skip,.command versionedHashesGuard,.command .skip]
def versionedHashesSuffix : ProgHOL 64:=.seq .skip (.seq versionedHashesGuard (.seq .skip .skip))

theorem versioned_hashes_shape : beforeVersionedHashes=CallPrefix.program versionedHashesActions beforeValidateHeader := by
  simp only [afterPayloadHeader,payloadHeaderCall,afterTransactionScan,transactionScanTail,afterTransactionCount,afterTransactionArray,
    transactionDeclarations,afterStateInit,afterCodes,afterNodes,nodeCall,afterHeaders,headerCall,afterPayload,body,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    CallPrefix.cut,↓reduceIte,blockHashAllocation,afterBlockHashAllocation,afterBlockHash,CallPrefix.program,
    afterBlockCompareResult,beforeVersionedHashes,versionedHashesContinuation,beforeValidateHeader,versionedHashesActions,
    versionedHashesArguments,versionedHashesGuard,localVar]
  trivial

theorem versioned_hashes_guard_pure : PureDecision versionedHashesGuard:=.ite _ (.raised _ _) .skip

theorem versioned_hashes_suffix_quiet (code) : ClockCost.Bound code versionedHashesSuffix 0:=
  ClockCost.sequence code .skip (.seq versionedHashesGuard (.seq .skip .skip)) 0 0 (ClockCost.skip code)
    (ClockCost.sequence code versionedHashesGuard (.seq .skip .skip) 0 0
      (ClockCost.conditional code _ _ _ 0 0 (ClockCost.raised code _ _) (ClockCost.skip code))
      (ClockCost.sequence code .skip .skip 0 0 (ClockCost.skip code) (ClockCost.skip code)))

theorem versioned_hashes_suffix_frame (code) : LocalEffects.Preserves code versionedHashesSuffix:=
  LocalEffects.sequence code .skip (.seq versionedHashesGuard (.seq .skip .skip)) (LocalEffects.skip code)
    (LocalEffects.sequence code versionedHashesGuard (.seq .skip .skip)
      (LocalEffects.conditional code _ _ _ (LocalEffects.raised code _ _) (LocalEffects.skip code))
      (LocalEffects.sequence code .skip .skip (LocalEffects.skip code) (LocalEffects.skip code)))

theorem versioned_hashes_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    ∃ callee,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) versionedHashesArguments=some [.val (.word si)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "is_valid_versioned_hashes") [.val (.word si)]=some (VersionedHashes.body,callee,.one) ∧
      Data input (callEntryStateHOLFinite source callee) pointer si record gasWord boundary := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) versionedHashesArguments=some [.val (.word si)]:=by
    simp [versionedHashesArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.siLocal]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "is_valid_versioned_hashes") (ofString "si") VersionedHashes.body .one si
    (VersionedHashes.original_code source.code data.arena.code)
  exact ⟨callee,args,called,data.of_frame rfl cell⟩

/-- The reached zero-count version checker and real BlockErr6 guard add
one caller source tick, including every setup read/shape failure and timeout. -/
theorem versioned_hashes_prefix_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program versionedHashesActions .skip)).2.clock≤1 := by
  obtain ⟨callee,args,called,entry⟩:=versioned_hashes_entry physical.data
  exact ClockCost.scoped_current source (ofString "vvh") .one (ofString "is_valid_versioned_hashes") versionedHashesArguments [.val (.word si)]
    VersionedHashes.body versionedHashesSuffix callee .one 0 0 args called (VersionedHashes.body_cost entry physical.transactionsZero)
    (versioned_hashes_suffix_quiet source.code)

theorem versioned_hashes_prefix_frame {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded) :
    LocalEffects.erase (evaluateHOLFiniteState source (CallPrefix.program versionedHashesActions .skip)).2=LocalEffects.erase source := by
  obtain ⟨callee,args,called,entry⟩:=versioned_hashes_entry physical.data
  exact LocalEffects.scoped_current source (ofString "vvh") .one (ofString "is_valid_versioned_hashes") versionedHashesArguments [.val (.word si)]
    VersionedHashes.body versionedHashesSuffix callee .one args called (VersionedHashes.body_frame entry physical.transactionsZero).metadata
    (versioned_hashes_suffix_frame source.code)

theorem versioned_hashes_reached {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (execution : CallPrefix.Execution source versionedHashesActions target) :
    AfterHeader input target pointer si record gasWord header boundary encoded := by
  have observed:=execution.erase .skip
  rw [evaluateHOLFiniteState_skip] at observed
  have frame : LocalEffects.erase target=LocalEffects.erase source:=observed.symm.trans (versioned_hashes_prefix_frame physical)
  have saved (key : MlS) (different : key≠ofString "vvh") : target.locals.lookup key=source.locals.lookup key:=by
    apply execution.keeps_local key
    intro action member
    simp [versionedHashesActions] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact CallPrefix.KeepsLocal.scoped key (ofString "vvh") .one (ofString "is_valid_versioned_hashes") versionedHashesArguments different
    · exact CallPrefix.KeepsLocal.decision key .skip .skip
    · exact CallPrefix.KeepsLocal.decision key versionedHashesGuard versioned_hashes_guard_pure
    · exact CallPrefix.KeepsLocal.decision key .skip .skip
  exact physical.of_frame frame ((saved _ (by decide)).trans physical.data.siLocal)
    ((saved _ (by decide)).trans physical.headerCell) ((saved _ (by decide)).trans physical.payloadCell)

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_guard_pure
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_suffix_quiet
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_suffix_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_reached

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual version checker/BlockErr6 guard either stops or exposes the
unchanged header-validation call with all physical main facts retained. -/
theorem versioned_hashes_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary encoded : Nat}
    (physical : AfterHeader input source pointer si record gasWord header boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeVersionedHashes=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ current inner,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeValidateHeader=(outcome,inner) := by
  rw [versioned_hashes_shape] at run
  rcases CallPrefix.priced_frame_trace source post versionedHashesActions beforeValidateHeader 1
    (versioned_hashes_prefix_cost physical) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    exact Or.inr ⟨current,inner,versioned_hashes_reached physical execution,forward,price,endpoint,continued⟩

/-- Complete original main prefix through the reached zero-count version
check and its actual rejection guard. Straight-line target work is separate. -/
theorem to_before_validate_header {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤479872713926 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤479872713926 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeValidateHeader=(outcome,inner) := by
  rcases to_before_versioned_hashes data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,header,encoded,physical,forward,price,endpoint,continued⟩:=reached
    rcases versioned_hashes_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,retained,checkForward,checkPrice,scope,rest⟩:=reached
      have scopeClock:=scope.clock
      exact Or.inr ⟨current,inner,header,encoded,retained,by omega,by omega,endpoint.trans scopeClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.versioned_hashes_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_before_validate_header

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_validate_header with | .function fn=>progToHOL fn.body | _=>.skip
def field (name : String) (offset : Nat) (shape : ShapeHOL:=.one) : ExpHOL 64:=
  .load shape (.op .add [localVar name,.const (BitVec.ofNat 64 offset)])
def zero (name : String) : ExpHOL 64:=.cmp .equal (localVar name) (.const 0#64)
def guard (tag : Nat) (test : ExpHOL 64) : ProgHOL 64:=.ite test (.raise (ofString "BlockErr") (.const (BitVec.ofNat 64 tag))) .skip
def guards : List (Nat×ExpHOL 64)→ ProgHOL 64→ ProgHOL 64
  | [],tail=>tail
  | (tag,test)::rest,tail=>.seq (guard tag test) (guards rest tail)
def nonceCheck : ExpHOL 64:=.cmp .lower (field "h" 96) (.const 1#64)
def excessChecks : List (Nat×ExpHOL 64):=
  [(21,.cmp .notEqual (field "h" 208) (localVar "ebg")),(22,.cmp .lower (field "h" 104) (field "h" 112))]
def baseArguments : List (ExpHOL 64):=
  [field "h" 104,field "parent" 104,field "parent" 112,field "parent" 160 RlpWrite.U256Value.tupleShape]
def feeArguments : List (ExpHOL 64):=[localVar "expected",field "h" 160 RlpWrite.U256Value.tupleShape]
def feeChecks : List (Nat×ExpHOL 64):=
  [(23,zero "eq"),(24,.cmp .notLower (field "parent" 120) (field "h" 120)),
    (25,.cmp .notEqual (field "h" 96) (.op .add [field "parent" 96,.const 1#64])),
    (26,.cmp .lower (.const 32#64) (field "h" 136))]
def mixCall : ProgHOL 64:=.call (some (some (.local,ofString "eq"),none)) (ofString "memeq")
  [field "h" 152,.var .global (ofString "hdr_zero8"),.const 8#64]
def afterZero (tail : ProgHOL 64) : ProgHOL 64:=.seq (guard 27 (zero "dz")) (.seq mixCall (.seq (guard 28 (zero "eq")) tail))
def afterExpected (tail : ProgHOL 64) : ProgHOL 64:=
  .decCall (ofString "eq") .one (ofString "u256_eq") feeArguments
    (guards feeChecks (.decCall (ofString "dz") .one (ofString "u256_is_zero") [field "h" 64 RlpWrite.U256Value.tupleShape] (afterZero tail)))
def afterExcess (tail : ProgHOL 64) : ProgHOL 64:=
  guards excessChecks (.decCall (ofString "expected") RlpWrite.U256Value.tupleShape (ofString "calculate_base_fee_per_gas") baseArguments (afterExpected tail))
def checkPrefix (tail : ProgHOL 64) : ProgHOL 64:=
  .seq (guard 20 nonceCheck) (.decCall (ofString "ebg") .one (ofString "calculate_excess_blob_gas") [localVar "parent"] (afterExcess tail))
def beforeMark : ProgHOL 64:=(CallPrefix.cutAt 14 body).2
def actions : List CallPrefix.Action:=
  [.command (guard 20 nonceCheck),.scoped (ofString "ebg") .one (ofString "calculate_excess_blob_gas") [localVar "parent"],
   .command (guard 21 (.cmp .notEqual (field "h" 208) (localVar "ebg"))),.command (guard 22 (.cmp .lower (field "h" 104) (field "h" 112))),
   .scoped (ofString "expected") RlpWrite.U256Value.tupleShape (ofString "calculate_base_fee_per_gas") baseArguments,
   .scoped (ofString "eq") .one (ofString "u256_eq") feeArguments,
   .command (guard 23 (zero "eq")),.command (guard 24 (.cmp .notLower (field "parent" 120) (field "h" 120))),
   .command (guard 25 (.cmp .notEqual (field "h" 96) (.op .add [field "parent" 96,.const 1#64]))),
   .command (guard 26 (.cmp .lower (.const 32#64) (field "h" 136))),
   .scoped (ofString "dz") .one (ofString "u256_is_zero") [field "h" 64 RlpWrite.U256Value.tupleShape],
   .command (guard 27 (zero "dz")),.command mixCall,.command (guard 28 (zero "eq"))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem body_shape : body=checkPrefix beforeMark := by
  simp only [body,Guest.Software.guestFn_validate_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,beforeMark,CallPrefix.cutAt,
    checkPrefix,afterExcess,excessChecks,afterExpected,feeArguments,baseArguments,feeChecks,
    afterZero,mixCall,guard,guards,nonceCheck,zero,field,RlpWrite.U256Value.tupleShape,localVar]

theorem prefix_shape (tail : ProgHOL 64) : CallPrefix.program actions tail=checkPrefix tail := by rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "validate_header")=some ([(ofString "parent",.one),(ofString "h",.one)],body,.one) := by
  have checked:=OriginalCode.indexed code installed 219
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_validate_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_validate_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem guard_decision (tag : Nat) (test : ExpHOL 64) : PureDecision (guard tag test):=.ite _ (.raised _ _) .skip

theorem guards_cost (code) (checks : List (Nat×ExpHOL 64)) (tail : ProgHOL 64) (price : Nat) (priced : ClockCost.Bound code tail price) :
    ClockCost.Bound code (guards checks tail) price := by
  induction checks with
  | nil=>exact priced
  | cons check rest ih=>
    rcases check with ⟨tag,test⟩
    simpa only [guards,Nat.zero_add] using ClockCost.sequence code _ _ 0 price (ClockCost.of_quiet code _ ((guard_decision tag test).quiet code)) ih

theorem guards_readonly (code) (checks : List (Nat×ExpHOL 64)) (tail : ProgHOL 64) (readonly : LocalEffects.Preserves code tail) :
    LocalEffects.Preserves code (guards checks tail) := by
  induction checks with
  | nil=>exact readonly
  | cons check rest ih=>
    exact LocalEffects.sequence code _ _ (LocalEffects.conditional code _ _ _ (LocalEffects.raised code _ _) (LocalEffects.skip code)) ih

theorem mix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code mixCall 33 :=
  MutableTable.MemeqAny.fixed_call_cost code installed (some (some (ofString "eq"))) _ _ 8 (by decide)

theorem mix_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code mixCall :=
  LocalEffects.call_body code (some (some (ofString "eq"))) _ _ _ _ _ (MutableTable.MemeqAny.original_code code installed)
    (MutableTable.MemeqAny.readonly code)

theorem after_zero_cost (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64) (price : Nat)
    (priced : ClockCost.Bound code tail price) : ClockCost.Bound code (afterZero tail) (33+price) := by
  have last : ClockCost.Bound code (.seq (guard 28 (zero "eq")) tail) price:=guards_cost code [(28,zero "eq")] tail price priced
  have copied:=ClockCost.sequence code mixCall _ 33 price (mix_cost code installed) last
  exact guards_cost code [(27,zero "dz")] _ (33+price) copied

theorem after_zero_readonly (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64)
    (readonly : LocalEffects.Preserves code tail) : LocalEffects.Preserves code (afterZero tail) := by
  have last : LocalEffects.Preserves code (.seq (guard 28 (zero "eq")) tail):=guards_readonly code [(28,zero "eq")] tail readonly
  exact guards_readonly code [(27,zero "dz")] _ (LocalEffects.sequence code _ _ (mix_readonly code installed) last)

theorem after_expected_cost (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64) (price : Nat)
    (priced : ClockCost.Bound code tail price) : ClockCost.Bound code (afterExpected tail) (35+price) := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  have dz : ClockCost.Bound code (.decCall (ofString "dz") .one (ofString "u256_is_zero") [field "h" 64 RlpWrite.U256Value.tupleShape] (afterZero tail)) (34+price):=by
    have result:=ClockCost.scoped_body code (ofString "dz") .one (ofString "u256_is_zero")
      [field "h" 64 RlpWrite.U256Value.tupleShape] (afterZero tail) _ _ _ 0 (33+price) (environment .u256_is_zero)
      (GasBudget.ArithmeticEffects.price_u256_is_zero code environment) (after_zero_cost code installed tail price priced)
    exact ClockCost.mono code _ _ _ result (by omega)
  have rest:=guards_cost code feeChecks _ (34+price) dz
  have result:=ClockCost.scoped_body code (ofString "eq") .one (ofString "u256_eq") feeArguments _ _ _ _ 0 (34+price)
    (environment .u256_eq) (GasBudget.ArithmeticEffects.price_u256_eq code environment) rest
  exact ClockCost.mono code _ _ _ result (by omega)

theorem after_expected_readonly (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64)
    (readonly : LocalEffects.Preserves code tail) : LocalEffects.Preserves code (afterExpected tail) := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  apply LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_eq)
    (GasBudget.ArithmeticEffects.original_preserves .u256_eq code environment)
  apply guards_readonly code feeChecks
  exact LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_is_zero)
    (GasBudget.ArithmeticEffects.original_preserves .u256_is_zero code environment) (after_zero_readonly code installed tail readonly)

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guard_decision
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guards_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guards_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.mix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.mix_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_zero_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_zero_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_expected_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_expected_readonly

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem guard_pure (tag : Nat) (test : ExpHOL 64) : PureGuard (guard tag test):=.ite _ (.raise _ _) .skip

/-- Rejected checks stop; skipped checks retain this exact source state. -/
theorem guards_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (checks : List (Nat×ExpHOL 64))
    (tail : ProgHOL 64) (price : Nat) (priced : source.clock-(evaluateHOLFiniteState source tail).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (guards checks tail)).2.clock≤price := by
  induction checks with
  | nil=>exact priced
  | cons check rest ih=>
    have bounded:=ClockCost.stopping_guard_current source check.2
      (.raise (ofString "BlockErr") (.const (BitVec.ofNat 64 check.1))) (guards rest tail) 0 price
      (NoFallthrough.raised _ _ source) (ClockCost.raised source.code _ _ source rfl) ih
    simpa only [guards,guard,Nat.zero_max] using bounded

theorem guards_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (checks : List (Nat×ExpHOL 64))
    (tail : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (guards checks tail)=(some (.returned value),post)) :
    evaluateHOLFiniteState source tail=(some (.returned value),post) := by
  induction checks with
  | nil=>exact normal
  | cons check rest ih=>
    exact ih ((guard_pure check.1 check.2).normal_continue source post (guards rest tail) value normal)

/-- The actual base-fee child is priced only at its real ABI entry. -/
theorem after_excess_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (tail : ProgHOL 64) (price : Nat) (priced : ClockCost.Bound source.code tail price) :
    source.clock-(evaluateHOLFiniteState source (afterExcess tail)).2.clock≤773+price := by
  unfold afterExcess
  apply guards_current
  have result:=ClockCost.scoped_arguments_current source (ofString "expected") RlpWrite.U256Value.tupleShape
    (ofString "calculate_base_fee_per_gas") baseArguments (afterExpected tail) 737 (35+price) (by
      intro values actual callee shape args called
      have bodyEq:=LocalEffects.lookup_body source.code (ofString "calculate_base_fee_per_gas") _ BaseFeeCurrent.body
        RlpWrite.U256Value.tupleShape (BaseFeeCurrent.original_code source.code installed) values actual callee shape called
      rw [bodyEq]
      exact BaseFeeCurrent.body_cost (callEntryStateHOLFinite source callee) base
        ⟨context.global,context.domain,context.arena,context.aligned⟩ installed)
    (after_expected_cost source.code installed tail price priced)
  omega

/-- Every outcome of the unchanged checkPrefix is covered, including failed
reads, invalid return shapes and short clocks. -/
theorem prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (tail : ProgHOL 64) (price : Nat) (priced : ClockCost.Bound source.code tail price) :
    source.clock-(evaluateHOLFiniteState source (checkPrefix tail)).2.clock≤450464+price := by
  unfold checkPrefix
  apply guards_current source [(20,nonceCheck)]
  have result:=ClockCost.scoped_arguments_reached_current source "ebg" .one (ofString "calculate_excess_blob_gas")
    [localVar "parent"] (afterExcess tail) 449690 (773+price) (by
      intro values actual callee shape args called
      have bodyEq:=LocalEffects.lookup_body source.code (ofString "calculate_excess_blob_gas") _ ExcessBlobCurrent.body .one
        (ExcessBlobCurrent.original_code source.code installed) values actual callee shape called
      rw [bodyEq]
      exact ExcessBlobCurrent.body_cost (callEntryStateHOLFinite source callee) base
        ⟨context.global,context.domain,context.arena,context.aligned⟩ installed) (by
      intro values actual callee shape target returned args called run valid
      have resumed:=ExcessBlobCurrent.resume source target base context installed "ebg" values actual callee shape called returned run
      rw [resumed.2]
      exact after_excess_cost (setVarHOLFinite (ofString "ebg") returned {source with memory:=target.memory,clock:=target.clock}) base
        ⟨context.global,context.domain,context.arena,context.aligned⟩ installed tail price priced)
  omega

/-- A genuine base-fee return retains metadata and every physical cell
outside its existing division workspace. -/
theorem after_excess_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (tail : ProgHOL 64) (price : Nat) (readonly : LocalEffects.Preserves source.code tail)
    (priced : ClockCost.Bound source.code tail price) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterExcess tail)=(some (.returned value),post)) :
    TaylorCurrent.WorkspaceResult source post base (773+price) := by
  have continued:=guards_returned source post excessChecks _ value normal
  have result:=TaylorCurrent.WorkspaceResult.scoped_normal source post base "expected" RlpWrite.U256Value.tupleShape
    (ofString "calculate_base_fee_per_gas") baseArguments (afterExpected tail) 737 (35+price) value continued (by
      intro values actual callee shape target returned args called run
      exact (BaseFeeCurrent.resume source target base context installed "expected" values actual callee shape called returned run).1) (by
      intro values actual callee shape target returned inner args called run valid rest
      have resumed:=BaseFeeCurrent.resume source target base context installed "expected" values actual callee shape called returned run
      rw [resumed.2] at rest ⊢
      exact TaylorCurrent.WorkspaceResult.of_readonly _ inner base (afterExpected tail) (35+price) (some (.returned value))
        (after_expected_readonly source.code installed tail readonly) (after_expected_cost source.code installed tail price priced) rest)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- The real excess-blob and base-fee children compose at their actual
remaining clocks, with lexical locals restored by the original evaluator. -/
theorem prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (tail : ProgHOL 64) (price : Nat) (readonly : LocalEffects.Preserves source.code tail)
    (priced : ClockCost.Bound source.code tail price) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (checkPrefix tail)=(some (.returned value),post)) :
    TaylorCurrent.WorkspaceResult source post base (450464+price) := by
  have continued:=(guard_pure 20 nonceCheck).normal_continue source post _ value normal
  have result:=TaylorCurrent.WorkspaceResult.scoped_normal source post base "ebg" .one
    (ofString "calculate_excess_blob_gas") [localVar "parent"] (afterExcess tail) 449690 (773+price) value continued (by
      intro values actual callee shape target returned args called run
      exact (ExcessBlobCurrent.resume source target base context installed "ebg" values actual callee shape called returned run).1) (by
      intro values actual callee shape target returned inner args called run valid rest
      have resumed:=ExcessBlobCurrent.resume source target base context installed "ebg" values actual callee shape called returned run
      rw [resumed.2] at rest ⊢
      exact after_excess_normal (setVarHOLFinite (ofString "ebg") returned {source with memory:=target.memory,clock:=target.clock}) inner base
        ⟨context.global,context.domain,context.arena,context.aligned⟩ installed
        tail price readonly priced value rest)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- Keep an actual caller binding through every original guard and scope. -/
theorem prefix_keeps (key : MlS) (ebg : key≠ofString "ebg") (expected : key≠ofString "expected")
    (eq : key≠ofString "eq") (dz : key≠ofString "dz") :
    ∀ action∈actions,CallPrefix.KeepsLocal key action := by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ ebg
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ expected
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ eq
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ dz
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)
  · intro source target reached
    cases reached with
    | command target command run=>
      have safe : LocalPrefix key mixCall:=.call (some (ofString "eq")) _ _ (by
        intro name same
        cases same
        exact eq)
      have summary:=safe.summary source
      rw [run] at summary
      exact summary.1 rfl
  · exact CallPrefix.KeepsLocal.decision key _ (guard_decision _ _)

/-- A reached checkPrefix has the same physical state as its genuine returning
probe. The probe changes only lexical restoration, which is erased here. -/
theorem prefix_reached (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (execution : CallPrefix.Execution source actions current) :
    TaylorCurrent.WorkspaceResult source current base 450464 ∧
      current.locals.lookup (ofString "h")=source.locals.lookup (ofString "h") ∧
      current.locals.lookup (ofString "parent")=source.locals.lookup (ofString "parent") := by
  let probe : ProgHOL 64:=.return (.const 0#64)
  let target:=(evaluateHOLFiniteState source (checkPrefix probe)).2
  have observed:=congrArg Prod.fst (execution.project probe)
  rw [prefix_shape] at observed
  have outcome : (evaluateHOLFiniteState source (checkPrefix probe)).1=some (.returned (.val (.word 0#64))):=by
    simpa [CallPrefix.project,probe,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL] using observed
  have run : evaluateHOLFiniteState source (checkPrefix probe)=(some (.returned (.val (.word 0#64))),target):=Prod.ext outcome rfl
  have frame:=prefix_normal source target base context installed probe 0
    (LocalEffects.returned source.code _) (ClockCost.returned source.code _) (.val (.word 0#64)) run
  have erased:=execution.erase probe
  rw [prefix_shape] at erased
  have same : LocalEffects.erase target=LocalEffects.erase current:=by
    simpa [target,probe,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,LocalEffects.erase,emptyLocalsHOLFinite] using erased
  have state:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=current.locals,memory:=current.memory,clock:=current.clock}) same.symm
  have old:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=current.locals,memory:=current.memory,clock:=current.clock}) frame.state
  have memory:=LocalEffects.memory_of_erase current target same
  have priced:=prefix_cost source base context installed .skip 0 (ClockCost.skip source.code)
  have clocks:=execution.skip_clock
  rw [prefix_shape] at clocks
  rw [clocks] at priced
  refine ⟨⟨state.trans old,?_,by simpa only [Nat.add_zero] using priced⟩,
    execution.keeps_local _ (prefix_keeps _ (by decide) (by decide) (by decide) (by decide)),
    execution.keeps_local _ (prefix_keeps _ (by decide) (by decide) (by decide) (by decide))⟩
  intro query outside
  rw [←memory]
  exact frame.away query outside

/-- The unchanged header checks either stop or reach their original heap
mark with the real header bindings and protected physical memory retained. -/
theorem prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤450464 ∨ ∃ current inner,
      TaylorCurrent.WorkspaceResult source current base 450464 ∧
      current.locals.lookup (ofString "h")=source.locals.lookup (ofString "h") ∧
      current.locals.lookup (ofString "parent")=source.locals.lookup (ofString "parent") ∧
      current.clock≤source.clock ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeMark=(outcome,inner) := by
  rw [body_shape,←prefix_shape] at run
  have priced:=prefix_cost source base context installed .skip 0 (ClockCost.skip source.code)
  rw [←prefix_shape] at priced
  rcases CallPrefix.priced_trace source post actions beforeMark 450464 (by simpa only [Nat.add_zero] using priced) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,cost,endpoint,continued⟩:=reached
    obtain ⟨frame,h,parent⟩:=prefix_reached source current base context installed execution
    exact Or.inr ⟨current,inner,frame,h,parent,forward,endpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guard_pure
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guards_current
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.guards_returned
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_excess_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.after_excess_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_keeps
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.prefix_trace

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def temporaryOutput : ExpHOL 64:=.op .add [localVar "tmp",.const 32#64]
def ommerByte : ProgHOL 64:=.storeByte (localVar "tmp") (.const 192#64)
def ommerHash : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") [localVar "tmp",.const 1#64,temporaryOutput]
def ommerCompare : ProgHOL 64:=.call (some (some (.local,ofString "eq"),none)) (ofString "memeq") [field "h" 16,temporaryOutput,.const 32#64]
def releaseMark : ProgHOL 64:=.call (some (none,none)) (ofString "heap_release") [localVar "mark"]
def ommerFailure : ProgHOL 64:=.seq releaseMark (.raise (ofString "BlockErr") (.const 29#64))
def ommerGuard : ProgHOL 64:=.ite (zero "eq") ommerFailure .skip
def ommerTail (tail : ProgHOL 64) : ProgHOL 64:=.seq ommerByte (.seq ommerHash (.seq ommerCompare (.seq ommerGuard tail)))
def ommerPrefix (tail : ProgHOL 64) : ProgHOL 64:=
  .decCall (ofString "mark") .one (ofString "heap_mark") []
    (.decCall (ofString "tmp") .one (ofString "alloc") [.const 64#64] (ommerTail tail))
def beforeParentHash : ProgHOL 64:=(CallPrefix.cutAt 6 beforeMark).2
def ommerActions : List CallPrefix.Action:=
  [.scoped (ofString "mark") .one (ofString "heap_mark") [],
   .scoped (ofString "tmp") .one (ofString "alloc") [.const 64#64],
   .command ommerByte,.command ommerHash,.command ommerCompare,.command ommerGuard]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ommer_shape : beforeMark=ommerPrefix beforeParentHash := by
  simp only [beforeMark,beforeParentHash,body,Guest.Software.guestFn_validate_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cutAt,
    ommerPrefix,ommerTail,ommerGuard,ommerFailure,releaseMark,ommerCompare,ommerHash,ommerByte,temporaryOutput,zero,field,localVar]

theorem ommer_prefix_shape (tail : ProgHOL 64) : CallPrefix.program ommerActions tail=ommerPrefix tail := by rfl

/-- The actual software hash length is the literal one-byte RLP marker.
Malformed temporary reads and failed ABI checks remain covered. -/
theorem ommer_hash_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code ommerHash 690 := by
  intro source codeEq
  have currentInstalled : OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  exact CurrentKeccak.Hash.dynamic_call_cost source (localVar "tmp") (.const 1#64) temporaryOutput 1 currentInstalled (by decide) rfl

theorem ommer_compare_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code ommerCompare 129 :=
  MutableTable.MemeqAny.fixed_call_cost code installed (some (some (ofString "eq"))) _ _ 32 (by decide)

theorem ommer_failure_stops : NoFallthrough ommerFailure:=NoFallthrough.sequence _ _ (NoFallthrough.raised _ _)

theorem ommer_guard_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code ommerGuard 1 := by
  have rejected : ClockCost.Bound code ommerFailure 1:=ClockCost.sequence code releaseMark _ 1 0
    (HeapScope.release_call_cost code installed (some none) [localVar "mark"]) (ClockCost.raised code _ _)
  exact ClockCost.conditional code _ _ _ 1 0 rejected (ClockCost.skip code)

/-- Snapshot, allocation, marker write, software hash, comparison and the
real rejecting release are priced on every original execution outcome. -/
theorem ommer_prefix_cost (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64) (price : Nat)
    (priced : ClockCost.Bound code tail price) : ClockCost.Bound code (ommerPrefix tail) (823+price) := by
  have last:=ClockCost.sequence code ommerGuard tail 1 price (ommer_guard_cost code installed) priced
  have compared:=ClockCost.sequence code ommerCompare _ 129 (1+price) (ommer_compare_cost code installed) last
  have hashed:=ClockCost.sequence code ommerHash _ 690 (129+(1+price)) (ommer_hash_cost code installed) compared
  have written:=ClockCost.sequence code ommerByte _ 0 (690+(129+(1+price)))
    (ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)) hashed
  have allocated:=PersistentAlloc.scoped_price code installed (ofString "tmp") .one [.const 64#64] _ _ written
  have marked:=ClockCost.scoped_body code (ofString "mark") .one (ofString "heap_mark") [] _ [] HeapScope.markBody .one 0 _
    (HeapScope.mark_original_code code installed) (HeapScope.mark_body_cost code) allocated
  exact ClockCost.mono code _ _ _ marked (by omega)

/-- A real normal ommer guard skipped its stopping failure branch. -/
theorem ommer_guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (normal : evaluateHOLFiniteState source ommerGuard=(none,target)) : target=source := by
  rcases conditional_none source target (zero "eq") ommerFailure .skip normal with rejected|skipped
  · exact (ommer_failure_stops source (congrArg Prod.fst rejected)).elim
  · simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm

/-- Retain the actual lexical trace for the remaining parent-header call;
its physical allocation/hash frame can be derived from this same trace. -/
theorem ommer_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source beforeMark=(outcome,post)) :
    source.clock-post.clock≤823 ∨ ∃ current inner,CallPrefix.Execution source ommerActions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤823 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeParentHash=(outcome,inner) := by
  rw [ommer_shape,←ommer_prefix_shape] at run
  have priced:=ommer_prefix_cost source.code installed .skip 0 (ClockCost.skip source.code) source rfl
  rw [←ommer_prefix_shape] at priced
  rcases CallPrefix.priced_trace source post ommerActions beforeParentHash 823 (by simpa only [Nat.add_zero] using priced) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · exact Or.inr reached

/-- Complete unchanged header prefix through both real fee calculations
and the empty-ommer hash check. The parent-hash suffix remains explicit. -/
theorem to_before_parent_hash (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤451287 ∨ ∃ feeEntry current inner,
      TaylorCurrent.WorkspaceResult source feeEntry base 450464 ∧
      feeEntry.locals.lookup (ofString "h")=source.locals.lookup (ofString "h") ∧
      feeEntry.locals.lookup (ofString "parent")=source.locals.lookup (ofString "parent") ∧
      CallPrefix.Execution feeEntry ommerActions current ∧ current.clock≤source.clock ∧
      source.clock-current.clock≤451287 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeParentHash=(outcome,inner) := by
  rcases prefix_trace source post base context installed outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨feeEntry,feePost,frame,h,parent,forward,endpoint,continued⟩:=reached
    have sameCode:=congrArg PanSemStateFiniteExact.code frame.state
    change feeEntry.code=source.code at sameCode
    have feeInstalled : OriginalCode.Installed feeEntry.code:=by rw [sameCode]; exact installed
    rcases ommer_trace feeEntry feePost feeInstalled outcome continued with stopped|reached
    · have price:=frame.cost
      exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,execution,hashForward,hashPrice,hashClock,rest⟩:=reached
      have price:=frame.cost
      exact Or.inr ⟨feeEntry,current,inner,frame,h,parent,execution,by omega,by omega,endpoint.trans hashClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_hash_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_compare_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_failure_stops
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_guard_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_guard_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.to_before_parent_hash

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def ommerCommands : List CallPrefix.Action:=[.command ommerByte,.command ommerHash,.command ommerCompare,.command ommerGuard]

private theorem local_command (key : MlS) (program : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key program source) :
    CallPrefix.KeepsLocal key (.command program) := by
  intro source target actual
  cases actual with
  | command target command run=>
    have summary:=safe source
    unfold LocalSummary at summary
    rw [run] at summary
    exact summary.1 rfl

theorem ommer_commands_keep (key : MlS) (eq : key≠ofString "eq") :
    ∀ action∈ommerCommands,CallPrefix.KeepsLocal key action := by
  intro action member
  simp only [ommerCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact local_command key _ (byte_store_local key _ _)
  · exact local_command key _ (LocalPrefix.call none _ _ (by intro name impossible; cases impossible)).summary_full
  · exact local_command key _ (LocalPrefix.call (some (ofString "eq")) _ _ (by
      intro name same
      cases same
      exact eq)).summary_full
  · intro source target actual
    cases actual with
    | command target command run=>rw [ommer_guard_normal source target run]

theorem ommer_keeps (key : MlS) (mark : key≠ofString "mark") (tmp : key≠ofString "tmp") (eq : key≠ofString "eq") :
    ∀ action∈ommerActions,CallPrefix.KeepsLocal key action := by
  intro action member
  change action∈CallPrefix.Action.scoped (ofString "mark") .one (ofString "heap_mark") []::
    CallPrefix.Action.scoped (ofString "tmp") .one (ofString "alloc") [.const 64#64]::ommerCommands at member
  simp only [List.mem_cons] at member
  rcases member with rfl|rfl|member
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ mark
  · exact CallPrefix.KeepsLocal.scoped key _ _ _ _ tmp
  · exact ommer_commands_keep key eq action member

theorem ommer_compare_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code ommerCompare :=
  LocalEffects.call_body code (some (some (ofString "eq"))) _ _ _ _ _ (MutableTable.MemeqAny.original_code code installed)
    (MutableTable.MemeqAny.readonly code)

/-- The actual marker/hash/comparison commands retain all globals and the
physical earlier-memory interval above the fixed arithmetic/hash workspace. -/
theorem ommer_commands_frame (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 64) (aligned : heap.toNat%8=0)
    (execution : CallPrefix.Execution source ommerCommands current) :
    CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64 ∧
      (∀ key,current.globals.lookup key=source.globals.lookup key) ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<heap.toNat→current.memory query=source.memory query := by
  obtain ⟨written,stored,afterWrite⟩:=execution.command_next ommerByte _
  obtain ⟨hashed,hashRun,afterHash⟩:=afterWrite.command_next ommerHash _
  obtain ⟨compared,compareRun,afterCompare⟩:=afterHash.command_next ommerCompare _
  obtain ⟨last,guardRun,finished⟩:=afterCompare.command_next ommerGuard []
  have lastEq : last=current:=by cases finished; rfl
  rw [lastEq] at guardRun
  have endpoint:=ommer_guard_normal compared current guardRun
  rw [endpoint]
  have read : eval source (localVar "tmp")=some (.val (.word heap)):=by simp [eval,evalHOLExact,toExact,localVar,temporary]
  have writeFrame:=byte_store_normal_frame source written (localVar "tmp") (.const 192#64) heap read stored
  have writtenEnvironment:=environment.after ommerByte none (fun key=>GlobalEffects.byte_store key source.code _ _) stored
  have writtenTmp : written.locals.lookup (ofString "tmp")=some (.val (.word heap)):=by rw [writeFrame.1]; exact temporary
  have arguments : evalListHOLFinite written (h:=fun query=>Classical.propDecidable (written.memaddrs query))
      [localVar "tmp",.const 1#64,temporaryOutput]=some (CurrentKeccak.Hash.values heap (heap+32#64) 1):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,temporaryOutput,writtenTmp,
      valueIsWord,valueWord,wordOpHOL,wordOp,CurrentKeccak.Hash.values]
  have outArena : AllocatedBytes.Arena (heap+32#64) 32:=AllocatedBytes.Arena.subrange heap 64 32 32 arena (by decide)
  have number : (heap+32#64).toNat=heap.toNat+32:=byteAddress_toNat heap 32 (by have bound:=arena.upper; omega)
  have hashedEnvironment:=writtenEnvironment.after ommerHash none
    (fun key=>CurrentKeccak.Hash.call_globals key written.code writtenEnvironment.installed _) hashRun
  have compareFrame:=ommer_compare_readonly hashed.code hashedEnvironment.installed hashed rfl
  rw [compareRun] at compareFrame
  change LocalEffects.erase compared=LocalEffects.erase hashed at compareFrame
  refine ⟨hashedEnvironment.of_frame compareFrame,?_,?_⟩
  · intro key
    have comparedGlobals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) compareFrame
    have hashedGlobals:=CurrentKeccak.Hash.call_globals key written.code writtenEnvironment.installed [localVar "tmp",.const 1#64,temporaryOutput] written rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState written ommerHash).2=GlobalEffects.erase key written at hashedGlobals
    rw [hashRun] at hashedGlobals
    have writtenGlobals : written.globals.lookup key=source.globals.lookup key:=by rw [writeFrame.1]
    exact comparedGlobals.trans ((congrArg Prod.snd hashedGlobals).trans writtenGlobals)
  · intro query above before
    have stateAway:=CopyGeneral.Away.before 2701132160#64 query 200 2701134824 (by decide) (by decide) above
    have padAway:=CopyGeneral.Away.before 2701132360#64 query 136 2701134824 (by decide) (by decide) above
    have outAway : CopyGeneral.Away (heap+32#64) query 32:=CopyGeneral.Away.after _ _ _
      (by rw [number]; omega) (by have bound:=outArena.upper; omega) (by rw [number]; omega)
    have hashedWord:=(CurrentKeccak.Hash.call_frame written hashed 2701132160#64 2701132360#64 heap (heap+32#64) query 1
      writtenEnvironment _ arguments (arena.weaken heap 64 1 (by decide)) outArena stateAway padAway outAway hashRun).memory
    have writtenWord:=writeFrame.2 query (by
      intro same
      have observed:=congrArg BitVec.toNat same
      rw [AllocatedBytes.aligned_number] at observed
      omega)
    exact (congrFun (LocalEffects.memory_of_erase hashed compared compareFrame) query).trans (hashedWord.trans writtenWord)

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_commands_keep
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_keeps
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_compare_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_commands_frame

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical state at the actual parent-header hash call. Allocation room
and both live temporary bindings come from the same reached execution. -/
structure OmmerReady (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  room : heap.toNat+64≤2952790016
  arena : AllocatedBytes.Arena heap 64
  environment : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64
  heapCell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64)))
  saved : current.locals.lookup (ofString "mark")=some (.val (.word heap))
  temporary : current.locals.lookup (ofString "tmp")=some (.val (.word heap))
  header : current.locals.lookup (ofString "h")=source.locals.lookup (ofString "h")
  parent : current.locals.lookup (ofString "parent")=source.locals.lookup (ofString "parent")
  globals : HeapGlobals source current
  memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<heap.toNat→current.memory query=source.memory query

/-- Expose the real mark and allocator return, derive its successful room,
and carry the actual marker/hash/comparison frame to the parent-hash entry. -/
theorem ommer_reached (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701134824≤heap.toNat) (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (execution : CallPrefix.Execution source ommerActions current) : OmmerReady source current heap := by
  change CallPrefix.Execution source (CallPrefix.Action.scoped (ofString "mark") .one (ofString "heap_mark") []::
    CallPrefix.Action.scoped (ofString "tmp") .one (ofString "alloc") [.const 64#64]::ommerCommands) current at execution
  have afterMark:=execution.heap_mark_next (ofString "mark") heap _ environment.installed heapCell
  let marked:=CallPrefix.heapMarked source (ofString "mark") heap
  change CallPrefix.Execution marked (CallPrefix.Action.scoped (ofString "tmp") .one (ofString "alloc") [.const 64#64]::ommerCommands) current at afterMark
  have arguments : evalListHOLFinite marked (h:=fun query=>Classical.propDecidable (marked.memaddrs query)) [.const 64#64]=
      some (PersistentAlloc.values 64#64):=rfl
  obtain ⟨room,commands⟩:=CallPrefix.Execution.alloc_next (source:=marked) (target:=current)
    (ofString "tmp") [.const 64#64] heap 64#64 ommerCommands environment.installed arguments heapCell bounded afterMark
  change heap.toNat+64≤2952790016 at room
  let allocated:=setVarHOLFinite (ofString "tmp") (.val (.word heap))
    (PersistentAlloc.post {marked with clock:=marked.clock-1} heap 64#64)
  change CallPrefix.Execution allocated ommerCommands current at commands
  have heapArena : AllocatedBytes.Arena heap 64:=⟨by omega,by omega⟩
  have allocatedGlobals (key : MlS) (different : key≠ofString "heap_ptr") : allocated.globals.lookup key=source.globals.lookup key:=by
    simp [allocated,marked,CallPrefix.heapMarked,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have allocatedEnvironment : CurrentKeccak.Hash.Environment allocated 2701132160#64 2701132360#64:=
    ⟨environment.installed,environment.domain,(allocatedGlobals _ (by decide)).trans environment.stateGlobal,
      (allocatedGlobals _ (by decide)).trans environment.padGlobal,environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩
  have allocatedTmp : allocated.locals.lookup (ofString "tmp")=some (.val (.word heap)):=by
    simp [allocated,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have allocatedMark : allocated.locals.lookup (ofString "mark")=some (.val (.word heap)):=by
    simp [allocated,marked,CallPrefix.heapMarked,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  obtain ⟨currentEnvironment,currentGlobals,earlierWords⟩:=ommer_commands_frame allocated current heap allocatedEnvironment allocatedTmp heapArena aligned commands
  refine ⟨room,heapArena,currentEnvironment,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [currentGlobals]
    simp [allocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · exact (commands.keeps_local _ (ommer_commands_keep _ (by decide))).trans allocatedMark
  · exact (commands.keeps_local _ (ommer_commands_keep _ (by decide))).trans allocatedTmp
  · exact execution.keeps_local _ (ommer_keeps _ (by decide) (by decide) (by decide))
  · exact execution.keeps_local _ (ommer_keeps _ (by decide) (by decide) (by decide))
  · intro key different
    exact (currentGlobals key).trans (allocatedGlobals key different)
  · intro query above before
    exact earlierWords query above before

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.ommer_reached

namespace InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original complete prefix exposes its real parent-hash entry with
both fee and temporary/hash physical frames from this same execution. -/
theorem to_parent_hash_physical (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base heap : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701134824≤heap.toNat) (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤451287 ∨ ∃ feeEntry current inner,
      TaylorCurrent.WorkspaceResult source feeEntry base 450464 ∧ OmmerReady feeEntry current heap ∧
      current.locals.lookup (ofString "h")=source.locals.lookup (ofString "h") ∧
      current.locals.lookup (ofString "parent")=source.locals.lookup (ofString "parent") ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤451287 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeParentHash=(outcome,inner) := by
  rcases to_before_parent_hash source post base context environment.installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨feeEntry,current,inner,frame,h,parent,execution,forward,price,endpoint,continued⟩:=reached
    have feeEnvironment : CurrentKeccak.Hash.Environment feeEntry 2701132160#64 2701132360#64:=by
      rw [frame.state]
      exact ⟨environment.installed,environment.domain,environment.stateGlobal,environment.padGlobal,
        environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩
    have feeHeap : feeEntry.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [frame.state]; exact heapCell
    have ready:=ommer_reached feeEntry current heap feeEnvironment feeHeap lower bounded aligned execution
    exact Or.inr ⟨feeEntry,current,inner,frame,ready,ready.header.trans h,ready.parent.trans parent,forward,price,endpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent

#print axioms InitECandidate.Solver.Input.CurrentVerify.HeaderValidateCurrent.to_parent_hash_physical

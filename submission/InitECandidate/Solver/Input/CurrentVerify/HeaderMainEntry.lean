import InitECandidate.Solver.Input.CurrentVerify.ExecutionRequests
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.CurrentVerify.StateReturnedData
import InitECandidate.Solver.Input.LoadWord

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_transaction_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_transaction_scan

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry PayloadHeaderWithdrawals

theorem payload_header_prefix_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : TransactionsNonempty input) :
    source.clock-(evaluateHOLFiniteState source (CallPrefix.program payloadHeaderActions .skip)).2.clock≤182601094624356403 := by
  obtain ⟨callee,args,called,entry⟩:=payload_header_entry data
  exact ClockCost.scoped_current source (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments [.val (.word si)]
    PayloadHeader.body .skip callee .one 182601094624356402 0 args called (PayloadHeaderBalance.body_cost entry checked) (ClockCost.skip source.code)

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
  encodedBound : encoded≤8388608

/-- The same actual normal hdr call supplies the returned header and all
nonlocal fields, then restores caller SI/PL and binds that exact hdr word. -/
theorem payload_header_reached_state {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (actual : CallPrefix.Reaches source (.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments) current) :
    ∃ header encoded,AfterHeader input current pointer si record gasWord header boundary encoded ∧ StateFrame source current header := by
  obtain ⟨callee,args,called,entry⟩:=payload_header_entry data
  obtain ⟨child,returned,run,endpoint⟩:=actual.scoped_known (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments
    [.val (.word si)] PayloadHeader.body callee .one args called
  obtain ⟨header,finished,encoded,physical,answer,scope,state⟩:=PayloadHeaderBalance.body_normal_state entry checked returned run
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
  refine ⟨header,encoded,⟨retained,currentHeader,currentPayload,physical.buffers,physical.geometry,
    (fun field member=>HeaderEncoding.FieldFacts.of_cells finished.memory current.memory header field cells (physical.fields field member)),
    (fun field member=>HeaderEncoding.FieldFacts.of_cells finished.memory current.memory header field cells (physical.optional field member)),
    physical.before,heapAfter,physical.sizeBound⟩,?_⟩
  rw [endpoint]
  exact ⟨state.entryHeap,state.globals,state.older⟩

/-- Physical projection of the same actual state-preserving call. -/
theorem payload_header_reached {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (actual : CallPrefix.Reaches source (.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments) current) :
    ∃ header encoded,AfterHeader input current pointer si record gasWord header boundary encoded := by
  obtain ⟨header,encoded,physical,_⟩:=payload_header_reached_state data payload checked actual
  exact ⟨header,encoded,physical⟩

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
theorem after_transaction_scan_header_state_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionScan=(outcome,post)) :
    source.clock-post.clock≤182601094624356403 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      PayloadHeaderEntry.StateFrame source current header ∧ current.clock≤source.clock ∧ source.clock-current.clock≤182601094624356403 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rw [payload_header_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at run
  rcases CallPrefix.priced_frame_trace source post payloadHeaderActions afterPayloadHeader 182601094624356403
    (payload_header_prefix_cost data checked) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    have actual : CallPrefix.Reaches source (.scoped (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments) current:=
      execution.singleton
    obtain ⟨header,encoded,physical,state⟩:=payload_header_reached_state data payload checked actual
    exact Or.inr ⟨current,inner,header,encoded,physical,state,forward,price,endpoint,continued⟩

theorem after_transaction_scan_header_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payload : source.locals.lookup (ofString "pl")=some (.val (.word record))) (checked : TransactionsNonempty input)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionScan=(outcome,post)) :
    source.clock-post.clock≤182601094624356403 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤182601094624356403 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rcases after_transaction_scan_header_state_trace data payload checked outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,header,encoded,physical,_,forward,price,scope,rest⟩:=reached
    exact Or.inr ⟨current,inner,header,encoded,physical,forward,price,scope,rest⟩

/-- The complete original run_attempt prefix through the real payload_header
return. This is a source-clock allowance, with all stopped outcomes included. -/
theorem to_after_payload_header {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤182602855438871939 ∨ ∃ current inner header encoded,
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤182602855438871939 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rcases to_after_transaction_scan data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,beforeData,payload,forward,price,endpoint,continued,checked⟩:=reached
    rcases after_transaction_scan_header_trace beforeData payload checked outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,header,encoded,physical,headerForward,headerPrice,scope,rest⟩:=reached
      have scopeClock:=scope.clock
      exact Or.inr ⟨current,inner,header,encoded,physical,by omega,by omega,endpoint.trans scopeClock,rest⟩

/-- The actual initialized records survive the complete original header
caller. Its interval frame also retains state/input contents above the
fixed hash workspaces; no header or allocation success is a premise. -/
theorem to_after_payload_header_with_records {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤182602855438871939 ∨ ∃ caller entered current inner ws bs header encoded,
      HasTables input caller pointer si record gasWord boundary ∧
      caller.globals.lookup (ofString "heap_ptr")=some (.val (.word ws)) ∧
      AfterHeader input current pointer si record gasWord header boundary encoded ∧
      Mpt.StateInit.MemoryContext entered ws ws bs ∧ Mpt.StateInit.MemoryContext current ws ws bs ∧ Mpt.WitnessCore.Stack.StablePrefix caller entered ws.toNat ∧
      PayloadHeaderEntry.StateFrame entered current header ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤182602855438871939 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterPayloadHeader=(outcome,inner) := by
  rcases to_after_transaction_scan_with_records data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,entered,target,ws,bs,tables,cell,beforeData,payload,records,older,forward,price,endpoint,continued,checked⟩:=reached
    rcases after_transaction_scan_header_state_trace beforeData payload checked outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,header,encoded,physical,frame,headerForward,headerPrice,scope,rest⟩:=reached
      have numbers:=physical.buffers.numbers header
      obtain ⟨heap,heapCell,lower,upper,aligned⟩:=physical.heapAfter
      have heapAfter : NormalHeapEffects.AtLeast header.toNat current:=⟨heap,heapCell,by rw [numbers.frontier] at lower; omega,upper,aligned⟩
      have retained:=frame.state_records records physical.data.arena heapAfter
      have scopeClock:=scope.clock
      exact Or.inr ⟨caller,entered,current,inner,ws,bs,header,encoded,tables,cell,physical,records,retained,older,frame,
        by omega,by omega,endpoint.trans scopeClock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_transaction_scan_header_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_payload_header


#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_reached_state
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_transaction_scan_header_state_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_payload_header_with_records

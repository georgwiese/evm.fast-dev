import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every outcome of the unchanged payload_header either stops within the
finite complete-prefix allowance or reaches its actual first indexed trie.
The reached caller retains its full physical input/header evidence, and the
actual computed-size guard supplies the accepted withdrawal-count cap. -/
theorem to_trie {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤396931061 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header continued inner encoded,PhysicalHeader input source continued pointer si record gasWord boundary header ∧
        encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
        continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
        continued.clock≤source.clock ∧ source.clock-continued.clock≤396931061 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState continued afterSizeGuard=(outcome,inner) := by
  rcases PayloadHeader.prefix_frame_trace source post data.arena.code outcome actual with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨current,outer,execution,forward,spent,endpoint,remaining⟩:=reached
    obtain ⟨header,physical⟩:=physical_header data execution
    rcases length_trace physical outcome remaining with stopped|reached
    · have cost:=stopped.1
      exact Or.inl ⟨by rw [endpoint.clock]; omega,stopped.2⟩
    · obtain ⟨continued,inner,lengthExecution,nextForward,lengthCost,nextEndpoint,afterLength⟩:=reached
      obtain ⟨encoded,minimum,number,bl,retained⟩:=length_reached physical lengthExecution
      rcases size_trace continued inner input encoded minimum bl number outcome afterLength with stopped|passed
      · have cost:=stopped.1
        exact Or.inl ⟨by rw [endpoint.clock,nextEndpoint.clock]; omega,stopped.2⟩
      · exact Or.inr ⟨header,continued,inner,encoded,retained,passed.1,passed.2.1,number,bl,by omega,by omega,
          endpoint.trans nextEndpoint,passed.2.2⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.to_trie


namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch PayloadHeaderEntry

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


/-- The actual parent call either stops at its child clock or resumes its
saved lexical continuation after a genuine checked header return. -/
def PayloadHeaderResumes (caller target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult outcome : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ value inner,childResult=some (.returned value) ∧
    (shapeEqHOL (shapeOfHOLExact value) .one && shapeEqHOL (shapeOfHOLExact value) .one)=true ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry caller target "hdr" value) afterPayloadHeader=(outcome,inner) ∧
    post=restore caller "hdr" inner

/-- A reached trie belongs to the same actual header child observed in
main's real call. Retain both the child suffix and parent continuation. -/
def AtTransactionTrie (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) (outcome : Option (PanSemResultExact 64)) : Prop :=
  ∃ callee target childResult header inner encoded,
    Data input (callEntryStateHOLFinite caller callee) pointer si record gasWord boundary ∧
    evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) PayloadHeader.body=(childResult,target) ∧
    PayloadHeaderResumes caller target post childResult outcome ∧
    PhysicalHeader input (callEntryStateHOLFinite caller callee) current pointer si record gasWord boundary header ∧
    encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
    current.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
    CallPrefix.ScopeFrame target inner ∧ evaluateHOLFiniteState current afterSizeGuard=(childResult,inner)

/-- The real scoped header call stops in its actual prefix or reaches its
first trie. No whole-header return or later trie success is assumed. -/
theorem after_transaction_scan_to_trie {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionScan=(outcome,post)) :
    source.clock-post.clock≤396931062 ∨ ∃ current,AtTransactionTrie input source current post pointer si record gasWord boundary outcome ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤396931062 := by
  obtain ⟨callee,args,called,entryData⟩:=payload_header_entry data
  rw [payload_header_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at run
  change evaluateHOLFiniteState source (.decCall (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments afterPayloadHeader)=(outcome,post) at run
  rcases CallNormal.scoped_observe source post "hdr" .one (ofString "payload_header") payloadHeaderArguments _ PayloadHeader.body
      afterPayloadHeader callee .one args called outcome run with stopped|observed
  · exact Or.inl (stopped.trans (by omega))
  · obtain ⟨childResult,target,funded,childRun,resumes⟩:=observed
    rcases PayloadHeaderEntry.to_trie entryData childResult childRun with stopped|reached
    · have price:=stopped.1
      change source.clock-1-target.clock≤396931061 at price
      rcases resumes with ended|⟨value,inner,returned,checked,continued,endpoint⟩
      · exact Or.inl (by omega)
      · exact (stopped.2 value returned).elim
    · obtain ⟨header,current,inner,encoded,physical,encodedBound,withdrawalBound,number,bl,forward,price,scope,continued⟩:=reached
      change current.clock≤source.clock-1 at forward
      change source.clock-1-current.clock≤396931061 at price
      exact Or.inr ⟨current,⟨callee,target,childResult,header,inner,encoded,entryData,childRun,resumes,physical,
        encodedBound,withdrawalBound,number,bl,scope,continued⟩,by omega,by omega⟩

/-- The complete current main prefix reaches the real transaction-trie
caller with retained input/header facts and both actual continuations. -/
theorem to_first_transaction_trie {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1761211446598 ∨ ∃ caller callerPost current,
      Data input caller pointer si record gasWord boundary ∧ TransactionsNonempty input ∧
      evaluateHOLFiniteState caller afterTransactionScan=(outcome,callerPost) ∧ post.clock=callerPost.clock ∧
      AtTransactionTrie input caller current callerPost pointer si record gasWord boundary outcome ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1761211446598 := by
  rcases to_after_transaction_scan data outcome run with stopped|reached
  · exact Or.inl (stopped.trans (by omega))
  · obtain ⟨caller,callerPost,currentData,payload,forward,price,endpoint,continued,checked⟩:=reached
    rcases after_transaction_scan_to_trie currentData outcome continued with stopped|entered
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,physical,nextForward,nextPrice⟩:=entered
      exact Or.inr ⟨caller,callerPost,current,currentData,checked,continued,endpoint,physical,by omega,by omega⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.payload_header_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_transaction_scan_to_trie
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_first_transaction_trie

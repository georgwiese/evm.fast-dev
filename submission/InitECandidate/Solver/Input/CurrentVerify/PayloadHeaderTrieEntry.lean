import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.ScopedCallObserve
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Mpt.CurrentIndexedLoop

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


namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual retained decoder image and successful original scan supply
owned nonempty rows for the fresh indexed builder. Mathematical input lists
remain unrestricted; only their already derived encoded extent is bounded. -/
theorem Data.indexed_transactions {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (checked : RunAttempt.TransactionsNonempty input)
    (before : boundary≤heap.toNat) :
    ∃ array count slices,source.memory (record+32#64)=.word array ∧ source.memory (record+40#64)=.word (BitVec.ofNat 64 count) ∧
      count=VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566) ∧ count≤12582752 ∧ Mpt.Indexed.SliceArray source array count heap.toNat 251655056 slices Mpt.CurrentIndexed.NonemptyRow := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  let count:=VarList.decodedCount input start size
  let slices:=fun index=>(VarList.recordPointer input pointer start index,VarList.recordLength input start size count index)
  obtain ⟨otherArray,otherStart,otherSize,block⟩:=data.block_inputs
  have sizeBound : size≤251655056:=by have inside:=payload.transactions.inside; have bounded:=block.inputBound; omega
  have lengths : ∀ index<count,VarList.recordLength input start size count index≠0#64:=by
    unfold RunAttempt.TransactionsNonempty at checked
    rw [←payload.transactions.startEq,←payload.transactions.sizeEq] at checked
    exact checked
  have geometry:=payload.transactions.records.slice_geometry source input pointer array start size
  obtain ⟨small,wordSmall,lengthCells⟩:=payload.transactions.records.cells source input pointer array start size data.arena.domain
  have pointers:=payload.transactions.records.pointer_cells source input pointer array start size
  have sizeActive (active : count≠0) : size≠0:=by
    intro zero
    have impossible : count=0:=by simp [count,VarList.decodedCount,zero]
    exact active impossible
  have arrayGeometry (active : count≠0) :=payload.transactions.records.array_geometry source input pointer array start size (sizeActive active)
  have countEq : count=VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566):=by
    dsimp only [count]
    rw [payload.transactions.startEq,payload.transactions.sizeEq]
  refine ⟨VarList.decodedArray array size,count,slices,payload.transactions.txs,payload.transactions.count,countEq,countBound,?_⟩
  constructor
  · intro active
    rw [VarList.decodedArray,if_neg (sizeActive active)]
    exact ⟨(arrayGeometry active).2.1,(arrayGeometry active).2.2.2.1⟩
  · intro active
    rw [VarList.decodedArray,if_neg (sizeActive active)]
    exact (arrayGeometry active).2.2.1
  · intro active
    rw [VarList.decodedArray,if_neg (sizeActive active)]
    have arrayAfter:=payload.transactions.arrayAfter
    have recordLower:=data.recordInside.1
    omega
  · intro active
    rw [VarList.decodedArray,if_neg (sizeActive active)]
    exact Nat.le_trans arrayBefore before
  · intro index inside
    exact ⟨pointers index inside,(lengthCells index inside).2⟩
  · intro index inside
    obtain ⟨number,extent,arena,arrayAfter⟩:=geometry index inside
    change (VarList.currentWord input start index).toNat+(VarList.recordLength input start size count index).toNat≤size at extent
    change Mpt.TrieWalk.Payload source.memaddrs (VarList.recordPointer input pointer start index) (VarList.recordLength input start size count index) 251655056
    refine ⟨by change (VarList.recordLength input start size count index).toNat≤251655056; omega,?_,?_⟩
    · have upper:=arena.upper
      omega
    · intro offset within
      exact AllocatedBytes.byte_mapped source _ _ offset data.arena.domain arena within
  · intro index inside
    refine ⟨?_,lengths index inside⟩
    intro zero
    change VarList.recordPointer input pointer start index=0#64 at zero
    have lower:=(geometry index inside).2.2.1.lower
    change 2701131776≤(VarList.recordPointer input pointer start index).toNat at lower
    rw [zero] at lower
    change 2701131776≤0 at lower
    omega

namespace PayloadHeaderEntry

def transactionTrieArguments : List (ExpHOL 64):=[payloadField 32,payloadField 40,localVar "txr"]
def transactionTrieCall : ProgHOL 64:=.call (some (none,none)) (ofString "build_mpt_indexed") transactionTrieArguments
def afterTransactionTrie : ProgHOL 64:=match afterSizeGuard with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem transaction_trie_shape : afterSizeGuard=.seq transactionTrieCall afterTransactionTrie:=by
  simp only [afterSizeGuard,PayloadHeader.afterLength,PayloadHeader.lengthCall,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    transactionTrieCall,transactionTrieArguments,afterTransactionTrie,payloadField,Scalar.plus,localVar] <;> rfl

/-- The literal first trie call receives its actual decoded rows, true
root destination and reached bounded heap. Every entry fact belongs to
the same physical prefix; no builder success is supplied. -/
theorem PhysicalHeader.transaction_entry {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input) :
    ∃ array count slices callee,
      evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) transactionTrieArguments=
        some (Mpt.Indexed.values array (BitVec.ofNat 64 count) (afterOmmerHeap header)) ∧
      lookupCodeHOLFinite current.code.lookup (ofString "build_mpt_indexed") (Mpt.Indexed.values array (BitVec.ofNat 64 count) (afterOmmerHeap header))=
        some (Mpt.Indexed.body,callee,.one) ∧ count=VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566) ∧ count≤12582752 ∧
      Nonempty (Mpt.CurrentIndexed.Entry (callEntryStateHOLFinite current callee) array count (afterOmmerHeap header) 251655056 slices) ∧
      Mpt.CurrentIndexed.RootInputs (callEntryStateHOLFinite current callee) (afterOmmerHeap header) 2701134640#64 := by
  have before : boundary≤(headerFrontier header).toNat:=by have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  obtain ⟨array,count,slices,arrayStored,countStored,countEq,countBound,rows⟩:=physical.data.indexed_transactions (heap:=headerFrontier header) checked before
  have plRead:=local_word_read current "pl" record physical.frame.payload
  have arrayRead:=Witness.load_word_read current (Scalar.plus (localVar "pl") 32) (record+32#64) array
    (Scalar.plus_read current (localVar "pl") record 32 plRead)
    (AllocatedBytes.word_mapped current record 136 32 physical.data.arena.domain physical.data.recordArena (by decide) physical.data.recordAligned (by decide)) arrayStored
  have countRead:=Witness.load_word_read current (Scalar.plus (localVar "pl") 40) (record+40#64) (BitVec.ofNat 64 count)
    (Scalar.plus_read current (localVar "pl") record 40 plRead)
    (AllocatedBytes.word_mapped current record 136 40 physical.data.arena.domain physical.data.recordArena (by decide) physical.data.recordAligned (by decide)) countStored
  have outRead:=local_word_read current "txr" (afterOmmerHeap header) physical.locals.transactions
  have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) transactionTrieArguments=
      some (Mpt.Indexed.values array (BitVec.ofNat 64 count) (afterOmmerHeap header)):=by
    simp only [eval] at arrayRead countRead outRead
    simp only [transactionTrieArguments,payloadField,Mpt.Indexed.values,evalListHOLFinite,evalListHOLExact,arrayRead,countRead,outRead]
  obtain ⟨callee,called,arrayLocal,countLocal,outLocal⟩:=Mpt.Indexed.environment current.code.lookup array (BitVec.ofNat 64 count) (afterOmmerHeap header)
    (Mpt.Indexed.original_code current.code physical.data.arena.code)
  let entry : Mpt.CurrentIndexed.Entry (callEntryStateHOLFinite current callee) array count (afterOmmerHeap header) 251655056 slices:={
    heap:=headerFrontier header,arrayCell:=arrayLocal,countCell:=countLocal,outCell:=outLocal,countBound:=by omega
    domain:=physical.data.arena.domain,little:=physical.data.little,installed:=physical.data.arena.code,keyGlobal:=physical.data.mptKey
    heapCell:=physical.frontier.cell,heapArena:=physical.frontier.arena,heapAligned:=physical.frontier.aligned
    heapAbove:=by have lower:=physical.data.recordInside.1; have a:=physical.data.recordInside.2; have b:=physical.before; have c:=physical.frontier.afterHeader; omega
    rows:=rows.of_band current _ array count (headerFrontier header).toNat 251655056 slices Mpt.CurrentIndexed.NonemptyRow rfl (by intros; rfl) }
  have roots : Mpt.CurrentIndexed.RootInputs (callEntryStateHOLFinite current callee) (afterOmmerHeap header) 2701134640#64:={
    arena:=⟨physical.data.arena.scratch,physical.data.arena.frame,physical.data.arena.domain,physical.data.arena.code⟩
    emptyGlobal:=physical.data.mptEmpty,emptyArena:=⟨by decide,by decide⟩,outArena:=physical.buffers.transactions }
  exact ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩

end PayloadHeaderEntry
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.indexed_transactions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_trie_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_entry

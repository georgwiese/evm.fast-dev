import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard
import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderTrieEntry
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Mpt.CurrentIndexedSetup
import InitECandidate.Solver.Input.CurrentVerify.DataMetadata
import InitECandidate.Solver.Input.HeaderEncoding.FieldFrame
import InitECandidate.Solver.WitnessRadix.AllocatedAwayBelow

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

/-- Retain the same physical header through an actual normal writer
whose metadata and caller locals are restored and whose writes lie beyond
the header's 31 cells. This also retains the whole earlier decoded input. -/
theorem PhysicalHeader.of_older {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (frame : MemoryMetadata.erase target=MemoryMetadata.erase current) (localsEq : target.locals=current.locals)
    (memory : ∀ query : BitVec 64,query.toNat<header.toNat+248→target.memory query=current.memory query) :
    PhysicalHeader input source target pointer si record gasWord boundary header := by
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=current.globals at globalsEq
  have domain:=MemoryMetadata.domain frame
  change target.memaddrs=current.memaddrs at domain
  have endian:=MemoryMetadata.endian frame
  change target.be=current.be at endian
  have code:=MemoryMetadata.code frame
  change target.code=current.code at code
  have cells (offset : Nat) (small : offset≤240) : target.memory (HeaderEncoding.address header offset)=current.memory (HeaderEncoding.address header offset):=by
    apply memory
    have number:=byteAddress_toNat header offset (by have upper:=physical.buffers.ommer.headerArena.upper; omega)
    change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at number
    change (header+BitVec.ofNat 64 offset).toNat<header.toNat+248
    omega
  exact {
    data:=physical.data.of_metadata frame (by rw [localsEq]; exact physical.data.siLocal)
      (fun query lower before=>memory query (by have headerBefore:=physical.before; omega))
    frame:={
      code:=code.trans physical.frame.code,domain:=domain.trans physical.frame.domain,endian:=endian.trans physical.frame.endian
      globals:=fun name other=>by rw [globalsEq]; exact physical.frame.globals name other
      header:=by rw [localsEq]; exact physical.frame.header
      raw:=by rw [localsEq]; exact physical.frame.raw
      payload:=by rw [localsEq]; exact physical.frame.payload
      si:=by rw [localsEq]; exact physical.frame.si
      older:=fun query lower before=>(memory query (by omega)).trans (physical.frame.older query lower before) }
    buffers:=physical.buffers,frontier:=physical.frontier.of_globals current target header (headerFrontier header) globalsEq
    before:=physical.before,geometry:=physical.geometry
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.fields field member)
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.optional field member)
    locals:=⟨by rw [localsEq]; exact physical.locals.transactions,by rw [localsEq]; exact physical.locals.withdrawals,
      by rw [localsEq]; exact physical.locals.requests,by rw [localsEq]; exact physical.locals.balance⟩ }

/-- The observed literal transaction-trie caller retains the complete
physical header and proves that the actual decoded transaction count is
zero. Its entry, normal callee and restored caller all belong to this run. -/
theorem PhysicalHeader.transaction_normal {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input)
    (normal : evaluateHOLFiniteState current transactionTrieCall=(none,target)) :
    VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0 ∧ PhysicalHeader input source target pointer si record gasWord boundary header ∧ target.locals=current.locals := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry checked
  obtain ⟨funded,child,returned,run⟩:=CallNormal.ignored_callee_return current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called normal
  obtain ⟨zero,answer,domain,endian,code,heapCell,globals,metadata,memory⟩:=Mpt.CurrentIndexed.body_normal entry roots returned run
  have endpoint:=CallNormal.ignored_target current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called returned child run normal
  have heapEq : entry.heap=headerFrontier header:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using entry.heapCell.symm.trans physical.frontier.cell
  have numbers:=physical.buffers.numbers header
  have outputAligned : (afterOmmerHeap header).toNat%8=0:=by rw [numbers.transactions]; have aligned:=physical.buffers.ommer.headerAligned; omega
  rw [endpoint]
  refine ⟨countEq.symm.trans zero,physical.of_older metadata rfl ?_,rfl⟩
  intro query before
  apply memory query
  · rw [heapEq,numbers.frontier]; omega
  · exact physical.buffers.transactions.away_below (afterOmmerHeap header) query 32 outputAligned (by rw [numbers.transactions]; omega)

/-- Main's literal first transaction-trie caller instantiates the complete
current builder allowance from its same decoded scan/header/startup evidence. -/
theorem PhysicalHeader.transaction_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input) :
    current.clock-(evaluateHOLFiniteState current transactionTrieCall).2.clock≤463385007916 := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry checked
  exact ClockCost.call_current current (some none) (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one 463385007915
    args called (Mpt.CurrentIndexed.uniform_body_cost entry roots countBound)

/-- The whole actual payload-header execution through its transaction
trie either stops within the combined allowance or reaches its unchanged
withdrawal suffix with zero transactions and all original physical inputs. -/
theorem to_after_transaction {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤463781938977 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,PhysicalHeader input source current pointer si record gasWord boundary header ∧
        VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0 ∧
        encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
        current.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤463781938977 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current afterTransactionTrie=(outcome,inner) := by
  rcases to_trie data outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,inner,encoded,physical,encodedBound,withdrawalBound,number,bl,forward,price,endpoint,remaining⟩:=reached
    rw [transaction_trie_shape,evaluateHOLFiniteState_seq_line780] at remaining
    have callPrice:=physical.transaction_cost checked
    have callForward:=evaluateHOLFiniteState_clock_le entered transactionTrieCall
    have never:=NoReturn.ignored_call (ofString "build_mpt_indexed") transactionTrieArguments entered
    generalize computed : evaluateHOLFiniteState entered transactionTrieCall=output at callPrice callForward remaining never
    obtain ⟨result,current⟩:=output
    change entered.clock-current.clock≤463385007916 at callPrice
    change current.clock≤entered.clock at callForward
    cases result with
    | none=>
      obtain ⟨zero,retained,localsEq⟩:=physical.transaction_normal checked computed
      exact Or.inr ⟨header,current,inner,encoded,retained,zero,encodedBound,withdrawalBound,number,
        by rw [localsEq]; exact bl,Nat.le_trans callForward forward,by omega,endpoint,remaining⟩
    | some result=>
      have observed:=congrArg Prod.fst remaining
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      change current.clock=inner.clock at clocks
      refine Or.inl ⟨by rw [endpoint,←clocks]; omega,?_⟩
      intro value returned
      apply never value
      change (evaluateHOLFiniteState entered transactionTrieCall).1=some (.returned value)
      rw [computed]
      exact observed.trans returned

end PayloadHeaderEntry
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.indexed_transactions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_trie_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.of_older
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.to_after_transaction

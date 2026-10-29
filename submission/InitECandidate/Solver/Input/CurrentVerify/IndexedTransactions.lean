import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Mpt.CurrentIndexedSetup

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
      count≤12582752 ∧ Mpt.Indexed.SliceArray source array count heap.toNat 251655056 slices Mpt.CurrentIndexed.NonemptyRow := by
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
  refine ⟨VarList.decodedArray array size,count,slices,payload.transactions.txs,payload.transactions.count,countBound,?_⟩
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
        some (Mpt.Indexed.body,callee,.one) ∧ count≤12582752 ∧
      Nonempty (Mpt.CurrentIndexed.Entry (callEntryStateHOLFinite current callee) array count (afterOmmerHeap header) 251655056 slices) := by
  have before : boundary≤(headerFrontier header).toNat:=by have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  obtain ⟨array,count,slices,arrayStored,countStored,countBound,rows⟩:=physical.data.indexed_transactions (heap:=headerFrontier header) checked before
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
  exact ⟨array,count,slices,callee,args,called,countBound,⟨entry⟩⟩

end PayloadHeaderEntry
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.indexed_transactions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_trie_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_entry

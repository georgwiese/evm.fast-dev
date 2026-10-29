import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderCompleted
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack PanSemStateFiniteExact WitnessRadix

private theorem rounded_number (pointer amount : BitVec 64) (aligned : pointer.toNat%8=0) (multiple : amount.toNat%8=0)
    (room : pointer.toNat+amount.toNat≤33806089496) :
    (PersistentAlloc.rounded pointer amount).toNat=pointer.toNat+amount.toNat := by
  rw [PersistentAlloc.rounded_nat pointer amount (by omega)]
  have sumAligned : (pointer.toNat+amount.toNat)%8=0:=by omega
  omega

structure BufferNumbers (heap : BitVec 64) : Prop where
  ommer : (ommerBase heap).toNat=heap.toNat+248
  temporary : (temporaryBase heap).toNat=heap.toNat+280
  transactions : (afterOmmerHeap heap).toNat=heap.toNat+288
  nonce : (zeroBase heap).toNat=heap.toNat+320
  withdrawals : (withdrawalBase heap).toNat=heap.toNat+328
  requests : (requestsBase heap).toNat=heap.toNat+360
  balance : (balanceBase heap).toNat=heap.toNat+392
  frontier : (headerFrontier heap).toNat=heap.toNat+424

/-- The eight original allocations reserve exactly424bytes. All natural
equalities follow from their real derived rooms and alignments. -/
theorem HeaderBuffers.numbers (heap : BitVec 64) (buffers : HeaderBuffers heap) : BufferNumbers heap := by
  have headerAligned:=buffers.ommer.headerAligned
  have ommer:=rounded_number heap 248#64 headerAligned (by decide) buffers.ommer.headerArena.upper
  change (ommerBase heap).toNat=heap.toNat+248 at ommer
  have temporary:=rounded_number (ommerBase heap) 32#64 buffers.ommer.ommerAligned (by decide) buffers.ommer.ommerArena.upper
  change (temporaryBase heap).toNat=(ommerBase heap).toNat+32 at temporary
  have transactions:=rounded_number (temporaryBase heap) 8#64 buffers.ommer.temporaryAligned (by decide) buffers.ommer.temporaryArena.upper
  change (afterOmmerHeap heap).toNat=(temporaryBase heap).toNat+8 at transactions
  have transactionAligned : (afterOmmerHeap heap).toNat%8=0:=by omega
  have nonce:=rounded_number (afterOmmerHeap heap) 32#64 transactionAligned (by decide) buffers.transactions.upper
  change (zeroBase heap).toNat=(afterOmmerHeap heap).toNat+32 at nonce
  have nonceAligned : (zeroBase heap).toNat%8=0:=by omega
  have withdrawals:=rounded_number (zeroBase heap) 8#64 nonceAligned (by decide) buffers.nonce.upper
  change (withdrawalBase heap).toNat=(zeroBase heap).toNat+8 at withdrawals
  have withdrawalAligned : (withdrawalBase heap).toNat%8=0:=by omega
  have requests:=rounded_number (withdrawalBase heap) 32#64 withdrawalAligned (by decide) buffers.withdrawals.upper
  change (requestsBase heap).toNat=(withdrawalBase heap).toNat+32 at requests
  have requestsAligned : (requestsBase heap).toNat%8=0:=by omega
  have balance:=rounded_number (requestsBase heap) 32#64 requestsAligned (by decide) buffers.requests.upper
  change (balanceBase heap).toNat=(requestsBase heap).toNat+32 at balance
  have balanceAligned : (balanceBase heap).toNat%8=0:=by omega
  have frontier:=rounded_number (balanceBase heap) 32#64 balanceAligned (by decide) buffers.balance.upper
  change (headerFrontier heap).toNat=(balanceBase heap).toNat+32 at frontier
  exact ⟨ommer,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩


def headerWords (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words) : List (BitVec 64):=[
  1#64,pointer+62#64,ommerBase heap,pointer+62#64+32#64,pointer+62#64+52#64,
  afterOmmerHeap heap,pointer+62#64+84#64,pointer+62#64+116#64,
  0#64,0#64,0#64,0#64,inputWord source record 80,inputWord source record 88,inputWord source record 96,inputWord source record 104,
  inputWord source record 16,inputWord source record 24,pointer+62#64+372#64,zeroBase heap,
  words 0,words 1,words 2,words 3,withdrawalBase heap,inputWord source record 112,inputWord source record 120,pointer+26#64,
  requestsBase heap,balanceBase heap,inputWord source record 128]

def headerWord (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words) (slot : Fin 31) : BitVec 64:=
  (headerWords source pointer record heap words)[slot.val]'(by simpa only [headerWords,List.length_cons,List.length_nil] using slot.isLt)

theorem cleared_zero_header (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (buffers : HeaderBuffers heap) (slot : Fin 31) :
    (clearedZero source hashed pointer record heap).memory (heap+BitVec.ofNat 64 (8*slot.val))=
      (beforeZero source hashed pointer record heap).memory (heap+BitVec.ofNat 64 (8*slot.val)) := by
  apply Zero.final_memory_away
  intro offset inside same
  have number:=byteAddress_toNat heap (8*slot.val) (by have h:=buffers.ommer.headerArena.upper; have s:=slot.isLt; omega)
  change (heap+BitVec.ofNat 64 (8*slot.val)).toNat=heap.toNat+8*slot.val at number
  have written:=byteAddress_toNat (zeroBase heap) offset (by have h:=buffers.nonce.upper; omega)
  have nonce:=(buffers.numbers heap).nonce
  have numeric:=congrArg BitVec.toNat same
  have small:=slot.isLt
  omega

set_option maxHeartbeats 1600000 in
/-- Every one of the31real header words, including live borrowed input
pointers, fresh output pointers and the actual base-fee limbs. -/
theorem complete_header_cells (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words) (buffers : HeaderBuffers heap)
    (output : OmmerHashOutput source pointer record heap hashed) (lower : 2701134824≤heap.toNat) (slot : Fin 31) :
    (completeHeader source hashed pointer record heap words).memory (heap+BitVec.ofNat 64 (8*slot.val))=
      .word (headerWord source pointer record heap words slot) := by
  have flag : hashed.memory heap=.word 1#64:=by
    simpa [initialHeaderWord] using output.cells source hashed pointer record heap buffers.ommer lower 0 (by decide)
  have parent : hashed.memory (heap+8#64)=.word (pointer+62#64):=by
    simpa [initialHeaderWord] using output.cells source hashed pointer record heap buffers.ommer lower 1 (by decide)
  have cleared:=cleared_zero_header source hashed pointer record heap buffers slot
  fin_cases slot <;> simp at cleared <;>
    simp [headerWord,headerWords,completeHeader,balancePointerStored,allocatedBalance,requestsPointerStored,allocatedRequests,
      beforeRequests,withdrawalScalarsStored,withdrawalScalarFields,withdrawalPointerStored,allocatedWithdrawal,
      baseFeeStored,wideStored,feeEntry,zeroPointerStored,putHeader,allocatedField,PersistentAlloc.post,setVarHOLFinite,
      cleared,beforeZero,scalarPrefixStored,payloadFieldsStored,scalarFields,wideZeroStored,bloomPointerStored,receiptsPointerStored,
      transactionPointerStored,allocatedTransactionRoot,stateRootStored,beneficiaryStored,ommerStored,StoreWord.put,flag,parent]

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderBuffers.numbers
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.cleared_zero_header
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.complete_header_cells

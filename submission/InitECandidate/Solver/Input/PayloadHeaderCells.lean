import InitECandidate.Solver.Input.PayloadHeaderBufferGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix
open Main

def headerWords (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) : List (BitVec 64):=[
  1#64,inputPointer+62#64,ommerBase heap,inputPointer+62#64+32#64,inputPointer+62#64+52#64,
  afterOmmerHeap heap,inputPointer+62#64+84#64,inputPointer+62#64+116#64,
  0#64,0#64,0#64,0#64,inputWord input source 80,inputWord input source 88,inputWord input source 96,inputWord input source 104,
  inputWord input source 16,inputWord input source 24,inputPointer+62#64+372#64,zeroBase heap,
  words 0,words 1,words 2,words 3,withdrawalBase heap,inputWord input source 112,inputWord input source 120,inputPointer+26#64,
  requestsBase heap,balanceBase heap,inputWord input source 128]

def headerWord (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) (slot : Fin 31) : BitVec 64:=
  (headerWords input source heap words)[slot.val]'(by simpa only [headerWords,List.length_cons,List.length_nil] using slot.isLt)

theorem cleared_zero_header (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (buffers : HeaderBuffers heap) (slot : Fin 31) :
    (clearedZero input source hashed heap).memory (heap+BitVec.ofNat 64 (8*slot.val))=
      (beforeZero input source hashed heap).memory (heap+BitVec.ofNat 64 (8*slot.val)) := by
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
theorem complete_header_cells (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) (buffers : HeaderBuffers heap)
    (output : OmmerHashOutput input source heap hashed) (lower : 2713717616≤heap.toNat) (slot : Fin 31) :
    (completeHeader input source hashed heap words).memory (heap+BitVec.ofNat 64 (8*slot.val))=
      .word (headerWord input source heap words slot) := by
  have flag : hashed.memory heap=.word 1#64:=by
    simpa [initialHeaderWord] using output.cells input source hashed heap buffers.ommer lower 0 (by decide)
  have parent : hashed.memory (heap+8#64)=.word (inputPointer+62#64):=by
    simpa [initialHeaderWord] using output.cells input source hashed heap buffers.ommer lower 1 (by decide)
  have cleared:=cleared_zero_header input source hashed heap buffers slot
  fin_cases slot <;> simp at cleared <;>
    simp [headerWord,headerWords,completeHeader,balancePointerStored,allocatedBalance,requestsPointerStored,allocatedRequests,
      beforeRequests,withdrawalScalarsStored,withdrawalScalarFields,withdrawalPointerStored,allocatedWithdrawal,
      baseFeeStored,wideStored,feeEntry,zeroPointerStored,storedField,allocatedField,PersistentAlloc.post,setVarHOLFinite,
      cleared,beforeZero,scalarPrefixStored,payloadFieldsStored,scalarFields,wideZeroStored,bloomPointerStored,receiptsPointerStored,
      transactionPointerStored,allocatedTransactionRoot,stateRootStored,beneficiaryStored,ommerStored,StoreWord.put,flag,parent]

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.cleared_zero_header
#print axioms InitECandidate.Solver.Input.PayloadHeader.complete_header_cells

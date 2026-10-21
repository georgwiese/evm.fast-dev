import InitECandidate.Solver.Input.RequestRootHashPrice
import InitECandidate.Solver.Input.MainHashingByteBudget

namespace InitECandidate.Solver.Input.Main.PayloadHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def description (input : Guest.InputBlob) : PayloadHash.Description where
  payload := PayloadPrefix.cursor input
  raw := inputPointer+62#64
  extra := inputPointer+602#64
  extraLength := Guest.GasLimit.le32 input 566-540
  transactions := VarList.decodedArray (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (Payload.transactionBytes input)
  transactionCount := Payload.transactionCount input
  transactionPointer := fun index=>VarList.recordPointer input inputPointer (62+Guest.GasLimit.le32 input 566) index
  transactionLength := fun index=>(VarList.recordLength input (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) (Payload.transactionCount input) index).toNat
  withdrawals := inputPointer+62#64+Payload.offsetWords input 2
  withdrawalCount := Payload.withdrawalCount input
  balance := inputPointer+62#64+Payload.offsetWords input 3
  balanceLength := ((PayloadPrefix.length input)-Payload.offsetWords input 3).toNat

/-- Every hasher-used payload cell is one of the actual original decoder
stores. This relates original data metadata, without invoking future hashes. -/
theorem cells_from_decoder (input : Guest.InputBlob) : ∀ cell∈(description input).cells,
    ∃ expression : ExpHOL 64,(cell.1,expression,cell.2)∈Payload.imageFields input inputPointer (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) := by
  intro cell member
  simp only [PayloadHash.Description.cells,description,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨localVar "p",List.mem_of_getElem? (i:=0) rfl⟩
  · exact ⟨Payload.extraPointerValue,List.mem_of_getElem? (i:=2) rfl⟩
  · exact ⟨Payload.extraLength,List.mem_of_getElem? (i:=3) rfl⟩
  · exact ⟨.rfield 0 (localVar "txs"),List.mem_of_getElem? (i:=4) rfl⟩
  · exact ⟨.rfield 1 (localVar "txs"),List.mem_of_getElem? (i:=5) rfl⟩
  · exact ⟨.op .add [localVar "p",localVar "o_wd"],List.mem_of_getElem? (i:=6) rfl⟩
  · exact ⟨localVar "nwd",List.mem_of_getElem? (i:=7) rfl⟩
  · exact ⟨.op .add [localVar "p",localVar "o_bal"],List.mem_of_getElem? (i:=8) rfl⟩
  · refine ⟨.op .sub [localVar "len",localVar "o_bal"],?_⟩
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact List.mem_of_getElem? (i:=9) rfl

/-- Actual normal main decoding supplies the complete payload hasher image,
including all real row pointers/length cells; empty arrays need no reads. -/
theorem image (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) (domain : current.memaddrs=InitE.ordinaryDomain) :
    (description input).Image current := by
  have bytes : Blob.HeapInput current input inputPointer := by
    obtain ⟨first,middleLower,ordered,lastUpper,codeArray,headerArray,heap,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,
      nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapWord,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := actual.decoded
    exact bytes
  constructor
  · intro cell member
    obtain ⟨expression,stored⟩ := cells_from_decoder input cell member
    exact actual.image (cell.1,expression,cell.2) stored
  · constructor
    intro index inside
    have pointer := (VarList.Records.pointer_reads current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
      (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) domain bytes actual.records index inside).2.1
    have length := (VarList.Records.cells current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
      (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) domain actual.records).2.2 index inside
    refine ⟨pointer,?_⟩
    have address (array : BitVec 64) : array+BitVec.ofNat 64 (16*index+8)=(array+BitVec.ofNat 64 (16*index))+8#64 := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc]
    change current.memory ((description input).transactions+BitVec.ofNat 64 (16*index+8))=.word (BitVec.ofNat 64 ((VarList.recordLength input (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) (Payload.transactionCount input) index).toNat))
    rw [address,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact length.2

end InitECandidate.Solver.Input.Main.PayloadHashData
#print axioms InitECandidate.Solver.Input.Main.PayloadHashData.cells_from_decoder
#print axioms InitECandidate.Solver.Input.Main.PayloadHashData.image

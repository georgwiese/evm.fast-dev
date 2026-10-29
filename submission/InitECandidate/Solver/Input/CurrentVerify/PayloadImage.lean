import InitECandidate.Solver.Input.CurrentHash.MainPayloadReturned
import InitECandidate.Solver.Input.CurrentStartup.MainDecodedTransactions

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual decoded payload cells and transaction records, retained before
main's original allocation boundary together with their proven input budget. -/
def PayloadImage (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (boundary : Nat) : Prop:=
  ∃ array length start size,Payload.ReturnedImage input source pointer record array length start size ∧
    array.toNat+16*VarList.decodedCount input start size≤boundary ∧ VarList.decodedCount input start size≤12582752 ∧
    VarList.sumPrefix (fun index=>(VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat)
      (VarList.decodedCount input start size)≤251655056

theorem PayloadImage.of_interval {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} {boundary : Nat} (image : PayloadImage input source pointer record boundary)
    (memory : ∀ query : BitVec 64,record.toNat≤query.toNat→query.toNat<boundary→target.memory query=source.memory query)
    (heap : NormalHeapEffects.AtLeast (boundary+32) target) : PayloadImage input target pointer record boundary := by
  obtain ⟨array,length,start,size,payload,before,count,bytes⟩:=image
  have extent : NormalHeapEffects.AtLeast (array.toNat+16*VarList.decodedCount input start size) target:=by
    obtain ⟨cursor,cell,lower,upper,aligned⟩:=heap
    exact ⟨cursor,cell,by omega,upper,aligned⟩
  exact ⟨array,length,start,size,payload.of_interval boundary before memory extent,before,count,bytes⟩

theorem PayloadImage.of_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} {boundary : Nat} (image : PayloadImage input source pointer record boundary)
    (frame : LocalEffects.erase target=LocalEffects.erase source) : PayloadImage input target pointer record boundary := by
  obtain ⟨array,length,start,size,payload,before,count,bytes⟩:=image
  exact ⟨array,length,start,size,payload.of_frame frame,before,count,bytes⟩

/-- Main's genuine root-hash return retains the complete payload image
already derived by the real decoder. Its transaction count/byte bounds are
reused from that same actual snapshot, without a fresh input restriction. -/
theorem main_payload_image {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : CurrentHash.RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : CurrentHash.WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") CurrentHash.RootEntry.arguments)=(none,post)) :
    PayloadImage input post origin.pointer record root.toNat := by
  obtain ⟨transactions,txStart,txSize,payload,before⟩:=ready.snapshot.payload_image
  obtain ⟨otherArray,otherStart,otherSize,otherImage,otherBefore,budget,count,bytes⟩:=ready.snapshot.transactions_bounded
  have sameStart : otherStart=txStart:=otherImage.startEq.trans payload.transactions.startEq.symm
  have sameSize : otherSize=txSize:=otherImage.sizeEq.trans payload.transactions.sizeEq.symm
  rw [sameStart,sameSize] at count bytes
  obtain ⟨arena,snapshot,heap,si⟩:=CurrentHash.RootHash.main_returned_state ready workspace actual
  have extent : NormalHeapEffects.AtLeast (root.toNat+32) post:=heap
  have arrayBefore : transactions.toNat+16*VarList.decodedCount input txStart txSize≤root.toNat:=by
    have afterRequest:=ready.rootAfter
    omega
  have recordLower : 2701134824≤record.toNat:=by
    obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,data,frame,clock⟩:=ready.snapshot
    have pointerLower:=data.context.pointerLower
    have statelessLower:=data.context.statelessLower
    have afterRecord:=data.context.recordAfter
    omega
  have image : PayloadImage input decoded origin.pointer record root.toNat:=⟨transactions,length,txStart,txSize,payload,arrayBefore,count,bytes⟩
  exact image.of_interval (by intro query lower upper; exact CurrentHash.RootHash.main_earlier_memory ready workspace actual query (by omega) upper) extent

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadImage.of_interval
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadImage.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.main_payload_image

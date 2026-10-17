import InitECandidate.Solver.Input.RlpLength.TransactionLoop
import InitECandidate.Solver.Input.VarList.RecordPointers

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Instantiate the actual loop using the real decoder result, including all
record pointers and conditional first-byte reads. Slice bytes are charged once. -/
theorem tx_decoded_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (lengthBound : length≤134217712)
    (domain : source.memaddrs=InitE.ordinaryDomain) (heap : Blob.HeapInput source input pointer)
    (records : VarList.Records source input pointer array start length)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array length))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (n : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word 0#64)))
    (code : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one))
    (enough : 12*VarList.decodedCount input start length≤source.clock) :
    ∃ target paid finalSum,paid≤12*VarList.decodedCount input start length ∧
      evaluateHOLFiniteState source transactionLoop=(none,target) ∧ target={source with locals:=target.locals,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))) ∧
      target.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 finalSum))) ∧
      finalSum≤length+9*VarList.decodedCount input start length ∧ finalSum≤436207564 ∧ (BitVec.ofNat 64 finalSum).toNat=finalSum ∧
      (∀ name : String,ofString "tl"≠ofString name→ ofString "i"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) := by
  classical
  let count:=VarList.decodedCount input start length
  let lengths:=VarList.recordLength input start length count
  let pointers:=VarList.recordPointer input pointer start
  let bytes:=VarList.recordFirstByte input start
  obtain ⟨countBound,countSmall,cells⟩:=records.cells source input pointer array start length domain
  obtain ⟨totalBound,sizes⟩:=records.size_bounds source input pointer array start length
  have pointersRead:=records.pointer_reads source input pointer array start length domain heap
  have txRecords : TxRecords source (VarList.decodedArray array length) lengths pointers bytes count := by
    intro index inside
    obtain ⟨mapped,stored⟩:=cells index inside
    obtain ⟨pointerMapped,pointerStored,loaded⟩:=pointersRead index inside
    exact ⟨mapped,stored,pointerMapped,pointerStored,loaded⟩
  have prefixBound : ∀ position≤count,VarList.sumPrefix (fun j=>(lengths j).toNat) position≤134217712 := by
    intro position inside
    have mono:=VarList.sum_prefix_mono (fun j=>(lengths j).toNat) position count inside
    change VarList.sumPrefix (fun j=>(lengths j).toNat) count≤length at totalBound
    omega
  obtain ⟨target,paid,finalSum,bound,run,frame,finalI,finalTL,upper,number,others⟩:=tx_loop_execute source (VarList.decodedArray array length)
    lengths pointers bytes 0 count count 0 (by omega) countSmall (by
      intro position inside
      have h:=sizes position inside
      change (lengths position).toNat≤length at h
      omega)
      prefixBound (by simp [VarList.sumPrefix]) txRecords txs i n tl code headerCode beCode enough
  change VarList.sumPrefix (fun j=>(lengths j).toNat) count≤length at totalBound
  refine ⟨target,paid,finalSum,bound,run,frame,finalI,finalTL,by omega,?_,number,others⟩
  change count≤length/4 at countBound
  omega

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_decoded_loop

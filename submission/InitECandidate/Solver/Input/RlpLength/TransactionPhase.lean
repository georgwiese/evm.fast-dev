import InitECandidate.Solver.Input.RlpLength.AfterTransactions

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def loopPhases : ProgHOL 64→List (ProgHOL 64)
  | code@(.seq first second)=>(match first with | .while _ _=>[code] | _=>[])++loopPhases first++loopPhases second
  | .dec _ _ _ inner | .decCall _ _ _ _ inner | .while _ inner=>loopPhases inner
  | .ite _ first second=>loopPhases first++loopPhases second
  | _=>[]
def transactionPhase : ProgHOL 64 := .seq transactionLoop transactionSuffix

theorem transaction_phase_subtree : ((loopPhases body)[0]?).getD .skip=transactionPhase := by
  simp only [loopPhases,body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some]
  rw [transactionPhase,transaction_loop_shape,transaction_suffix_shape]
  rw [afterTransactionHeader,enterWithdrawals,withdrawalPhase,loop_shape,suffix_shape]
  rfl

/-- Actual block tail from the first transaction-loop test through return.
Decoded records establish transaction loads and aggregate size; the preceding
encoded-header bound and phase entry are still explicit. -/
theorem transaction_phase_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload : BitVec 64) (txStart txLength wdStart wdCount total : Nat)
    (txLengthBound : txLength≤134217712) (wdSmall : wdCount<2^31) (totalSmall : total≤2^31)
    (domain : source.memaddrs=InitE.ordinaryDomain) (heap : Blob.HeapInput source input pointer)
    (records : VarList.Records source input pointer array txStart txLength) (inside : wdStart+44*wdCount≤input.length%2^64)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array txLength))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (n : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength)))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word 0#64)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (t : source.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))))
    (mappedCount : source.memaddrs (payload+56#64)) (storedCount : source.memory (payload+56#64)=.word (BitVec.ofNat 64 wdCount))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 wdStart))
    (bytesCode : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one))
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one))
    (enough : 12*VarList.decodedCount input txStart txLength+43*wdCount+33≤source.clock) :
    ∃ target encoded paid,25*wdCount≤encoded ∧ encoded≤total+436207564+57*wdCount+28 ∧
      paid≤12*VarList.decodedCount input txStart txLength+43*wdCount+33 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source transactionPhase=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  obtain ⟨next,loopPaid,txSum,loopBound,loopRun,frame,finalI,finalTL,txUpper,txBound,txNumber,others⟩:=
    tx_decoded_loop source input pointer array txStart txLength txLengthBound domain heap records txs i n tl bytesCode headerCode beCode (by omega)
  have nextClock:=congrArg PanSemStateFiniteExact.clock frame
  change next.clock=source.clock-loopPaid at nextClock
  have nextCode:=congrArg PanSemStateFiniteExact.code frame
  change next.code=source.code at nextCode
  have nextMem:=congrArg PanSemStateFiniteExact.memory frame
  change next.memory=source.memory at nextMem
  have nextDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change next.memaddrs=source.memaddrs at nextDomain
  have nextBE:=congrArg PanSemStateFiniteExact.be frame
  change next.be=source.be at nextBE
  have nextHeap:=Blob.HeapInput.of_fields source next input pointer nextMem.symm nextDomain.symm nextBE.symm heap
  have nextPL : next.locals.lookup (ofString "pl")=some (.val (.word payload)) :=
    (others "pl" (by decide) (by decide)).trans pl
  have nextTotal : next.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))) :=
    (others "total" (by decide) (by decide)).trans t
  obtain ⟨target,encoded,tailPaid,lower,upper,tailBound,number,tailRun,tailFrame⟩:=after_transactions_execute next input pointer payload
    (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength)) wdStart wdCount total txSum wdSmall totalSmall txBound nextHeap inside nextPL finalI nextTotal finalTL
      (by rw [nextDomain]; exact mappedCount) (by rw [nextMem]; exact storedCount) (by rw [nextDomain]; exact mapped) (by rw [nextMem]; exact stored)
      (by rw [nextCode]; exact code) (by rw [nextCode]; exact wordCode) (by rw [nextCode]; exact listCode)
      (by rw [nextCode]; exact headerCode) (by rw [nextCode]; exact beCode) (by omega)
  refine ⟨target,encoded,loopPaid+tailPaid,lower,by omega,by omega,number,?_,?_⟩
  · rw [transactionPhase,WitnessRadix.StateSteps.next_sequence source next _ _ loopRun (by omega)]
    exact tailRun
  · have transfer : emptyLocalsHOLFinite {next with clock:=next.clock-tailPaid}=
        emptyLocalsHOLFinite {source with clock:=source.clock-loopPaid-tailPaid} := by rw [frame]; rfl
    have subtract : source.clock-loopPaid-tailPaid=source.clock-(loopPaid+tailPaid) := by omega
    exact tailFrame.trans (transfer.trans (congrArg (fun clock=>emptyLocalsHOLFinite {source with clock:=clock}) subtract))

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.transaction_phase_subtree
#print axioms InitECandidate.Solver.Input.RlpLength.Block.transaction_phase_execute

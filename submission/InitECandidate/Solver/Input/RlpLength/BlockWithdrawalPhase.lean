import InitECandidate.Solver.Input.RlpLength.BlockSuffix

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def withdrawalPhase : ProgHOL 64 := .seq withdrawalLoop withdrawalSuffix

/-- The actual final withdrawal loop and block-length suffix. Entry into this
phase, including the preceding transaction/header total bound, is explicit. -/
theorem withdrawal_phase_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer payload old : BitVec 64) (start count total : Nat) (countSmall : count<2^31) (totalSmall : total≤2^32)
    (heap : Blob.HeapInput source input pointer) (inside : start+44*count≤input.length%2^64)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (n : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))))
    (wl : source.locals.lookup (ofString "wl")=some (.val (.word 0#64)))
    (t : source.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))))
    (hl : source.locals.lookup (ofString "hl")=some (.val (.word old)))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 start))
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 43*count+22≤source.clock) :
    ∃ target encoded paid,25*count≤encoded ∧ encoded≤total+57*count+18 ∧ paid≤43*count+22 ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source withdrawalPhase=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  obtain ⟨next,loopPaid,sum,loopBound,loopRun,frame,finalI,finalWL,lower,upper,number,others⟩:=
    loop_execute source input pointer payload start 0 count count 0 (by omega) countSmall (by omega) (by omega) heap inside pl i n wl
      mapped stored code wordCode listCode headerCode beCode (by omega)
  have nextClock:=congrArg PanSemStateFiniteExact.clock frame
  change next.clock=source.clock-loopPaid at nextClock
  have nextCode:=congrArg PanSemStateFiniteExact.code frame
  change next.code=source.code at nextCode
  have nextTotal : next.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))) :=
    (others "total" (by decide) (by decide)).trans t
  have nextHeader : next.locals.lookup (ofString "hl")=some (.val (.word old)) :=
    (others "hl" (by decide) (by decide)).trans hl
  obtain ⟨target,encoded,tailPaid,encodedLower,encodedUpper,tailBound,encodedNumber,tailRun,tailFrame⟩:=
    suffix_execute next count sum total old countSmall lower upper totalSmall finalWL nextTotal nextHeader
      (by rw [nextCode]; exact listCode) (by rw [nextCode]; exact headerCode) (by rw [nextCode]; exact beCode) (by omega)
  refine ⟨target,encoded,loopPaid+tailPaid,encodedLower,by omega,by omega,encodedNumber,?_,?_⟩
  · rw [withdrawalPhase,WitnessRadix.StateSteps.next_sequence source next _ _ loopRun (by omega)]
    exact tailRun
  · have transfer : emptyLocalsHOLFinite {next with clock:=next.clock-tailPaid}=
        emptyLocalsHOLFinite {source with clock:=source.clock-loopPaid-tailPaid} := by
      rw [frame]
      rfl
    have subtract : source.clock-loopPaid-tailPaid=source.clock-(loopPaid+tailPaid) := by omega
    exact tailFrame.trans (transfer.trans (congrArg (fun clock=>emptyLocalsHOLFinite {source with clock:=clock}) subtract))

/-- Size guard consequence once the actual phase result is known. -/
theorem withdrawal_count_of_length (count encoded : Nat) (minimum : 25*count≤encoded) (sizeGuard : encoded≤8388608) :
    count≤335544 := by omega

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.withdrawal_phase_execute
#print axioms InitECandidate.Solver.Input.RlpLength.Block.withdrawal_count_of_length

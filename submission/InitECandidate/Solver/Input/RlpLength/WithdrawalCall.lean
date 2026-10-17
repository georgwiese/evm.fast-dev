import InitECandidate.Solver.Input.RlpLength.WithdrawalBuilt

namespace InitECandidate.Solver.Input.RlpLength.Withdrawal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual withdrawal size call from copied bytes. Its result and exact
read-only caller entry support no-wrap accumulation in block_rlp_length. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+44≤input.length%2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word (pointer+BitVec.ofNat 64 start))])
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (formals,body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 42≤source.clock) :
    ∃ encoded paid,25≤encoded ∧ encoded≤57 ∧ paid≤41 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "withdrawal_rlp_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨callee,called,wd⟩:=CallNormal.unary_environment source.code.lookup (ofString "withdrawal_rlp_len") "wd" body (pointer+BitVec.ofNat 64 start) code
  let entry:=callEntryStateHOLFinite source callee
  have entryHeap : Blob.HeapInput entry input pointer:=Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame⟩:=execute entry input pointer start entryHeap inside wd wordCode listCode headerCode beCode
    (by change 41≤source.clock-1; omega)
  exact ⟨encoded,paid,lower,upper,bound,CallNormal.pure_return_execute source target name (ofString "withdrawal_rlp_len") expressions
    [.val (.word (pointer+BitVec.ofNat 64 start))] body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpLength.Withdrawal

#print axioms InitECandidate.Solver.Input.RlpLength.Withdrawal.call_execute

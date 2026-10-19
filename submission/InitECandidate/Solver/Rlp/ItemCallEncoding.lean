import InitECandidate.Solver.Rlp.ItemCallFrame
import InitECandidate.Solver.Rlp.ItemEncodingNormal

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual returned quad determines its header, payload and flag. -/
theorem result_injective (pointer h p f h' p' f' : BitVec 64)
    (same : result pointer h p f=result pointer h' p' f') : h=h' ∧ p=p' ∧ f=f' := by
  simp only [result,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,BitVec.add_right_inj] at same
  exact ⟨same.2.1,same.2.2.1,same.1⟩

/-- A genuine original item call retains the input encoding that produced
its actual tuple, in addition to the arena, memory frame and paid price. -/
theorem scoped_normal_encoded (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost header payload flag inner,
      Valid pointer length.toNat (result pointer header payload flag) ∧ Header.Encoded source pointer header payload flag ∧ Validation.Arena calleePost cursor limit ∧
      Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      source.clock-calleePost.clock≤60*length.toNat+42 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (result pointer header payload flag)) continuation=
        (some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨header,payload,flag,answerEq,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,price⟩ :=
    body_frame (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
      (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  obtain ⟨encodedHeader,encodedPayload,encodedFlag,encoded,encodingEq⟩ :=
    body_encoding (callEntryStateHOLFinite source callee) calleePost pointer pointerLocal installed answer bodyRun
  have same := result_injective pointer header payload flag encodedHeader encodedPayload encodedFlag (answerEq.symm.trans encodingEq)
  rcases same with ⟨rfl,rfl,rfl⟩
  rw [answerEq] at continuationRun
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+41 at price
  exact ⟨positive,calleePost,header,payload,flag,inner,valid,encoded,nextArena,above,domainEq,endianEq,codeEq,heapEq,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.result_injective
#print axioms InitECandidate.Solver.Rlp.Item.scoped_normal_encoded

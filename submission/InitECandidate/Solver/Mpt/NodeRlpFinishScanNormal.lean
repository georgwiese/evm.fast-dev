import InitECandidate.Solver.Mpt.NodeRlpFinishScanCost
import InitECandidate.Solver.Input.ScopedCallNoneData
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scan_body_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code scanBody := by
  rw [scan_shapes.2.1]
  exact Input.LocalEffects.scoped_body code (ofString "rl2") .one (ofString "node_ref_len") childArguments (.seq addLength advance)
    NodeRefLen.formals NodeRefLen.body .one (NodeRefLen.original_code code installed) (NodeRefLen.readonly code installed)
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _))

/-- A real scan iteration derives its <=33-byte addition from the actual
reference helper, then performs the genuine payload and counter updates. -/
theorem scan_iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (normal : evaluateHOLFiniteState source scanBody=(none,target)) :
    ∃ added : BitVec 64,added.toNat≤33 ∧ target.locals.lookup (ofString "i")=some (.val (.word (index+1#64))) ∧
      target.locals.lookup (ofString "payload")=some (.val (.word (payload+added))) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have shaped:=normal
  rw [scan_shapes.2.1] at shaped
  obtain ⟨funded,values,body,callee,shape,childTarget,returned,inner,args,called,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none_data source target "rl2" .one (ofString "node_ref_len") childArguments (.seq addLength advance) shaped
  let current:=Input.CallNormal.continuationEntry source childTarget "rl2" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "rl2") .one (ofString "node_ref_len") childArguments) current:=
    .scoped source _ _ _ _ values body callee shape returned childTarget args called (by omega) run checked
  obtain ⟨added,bounded,lengthCell,saved,_frame,_price⟩:=NodeRefLen.scoped_normal (ofString "rl2") childArguments installed reached
  have currentPayload : current.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (saved (ofString "payload") (by decide)).trans payloadCell
  obtain ⟨afterAdd,addRun,advanceRun⟩:=Input.sequence_none current inner addLength advance continued
  have read : eval current (.op .add [localVar "payload",localVar "rl2"])=some (.val (.word (payload+added))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,currentPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have afterAddEq:=Input.assign_none current afterAdd "payload" (.op .add [localVar "payload",localVar "rl2"]) (payload+added) read addRun
  have keep:= (Input.LocalPrefix.assign (key:=ofString "payload") (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full afterAdd
  change Input.LocalSummary (ofString "payload") advance afterAdd at keep
  unfold Input.LocalSummary at keep
  rw [advanceRun] at keep
  have finalPayload : inner.locals.lookup (ofString "payload")=some (.val (.word (payload+added))):=by
    rw [keep.1 rfl,afterAddEq]
    exact bind_lookup_same _ _ _
  have frame:=scan_body_readonly source.code installed source rfl
  rw [normal] at frame
  refine ⟨added,bounded,scan_body_advance source target index indexCell normal,?_,frame⟩
  rw [endpoint,restore_lookup_other source inner "rl2" "payload" (by decide)]
  exact finalPayload

/-- Sixteen real reference results contribute at most528 bytes in total.
The source payload and this bound prove that the actual additions do not
wrap. The scan leaves every nonlocal field unchanged. -/
theorem scan_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (fits : payload.toNat+528<2^64)
    (normal : evaluateHOLFiniteState source scanLoop=(none,target)) :
    (∃ result : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word result)) ∧ result.toNat≤payload.toNat+528) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ index value : BitVec 64,
    current.locals.lookup (ofString "i")=some (.val (.word index)) ∧ current.locals.lookup (ofString "payload")=some (.val (.word value)) ∧
      index.toNat≤16 ∧ value.toNat≤payload.toNat+33*index.toNat
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) scanBody=(none,post)→invariant post:=by
    intro current codeEq ⟨index,value,indexCell,payloadCell,bounded,amount⟩ word observed nonzero _funded post run
    have small : index.toNat<9223372036854775808:=by omega
    have expected : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=
        some (.val (.word (if index.toNat<16 then 1#64 else 0#64))):=by
      simp [scanTest,evalHOLFinite,evalHOLExact,toExact,localVar,indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]
    have active : index.toNat<16:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using observed.symm.trans expected
      exact nonzero zero
    have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    obtain ⟨added,bound,indexAfter,payloadAfter,_frame⟩:=scan_iteration_normal (decClockHOLFinite current) post index value currentInstalled indexCell payloadCell run
    have indexNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]; rfl
    have amountNumber : (value+added).toNat=value.toNat+added.toNat:=BitVec.toNat_add_of_lt (by omega)
    exact ⟨index+1#64,value+added,indexAfter,payloadAfter,by rw [indexNumber]; omega,by rw [amountNumber,indexNumber]; omega⟩
  have shaped:=normal
  rw [scan_shapes.1] at shaped
  obtain ⟨index,result,_indexAfter,payloadAfter,bounded,amount⟩:=Input.loop_invariant source.code (ofString "node") scanTest scanBody scan_body_safe invariant step source target rfl
    ⟨0#64,payload,indexCell,payloadCell,by decide,by simp⟩ shaped
  have frame:=Input.LocalEffects.loop source.code scanTest scanBody (scan_body_readonly source.code installed) source rfl
  rw [shaped] at frame
  exact ⟨⟨result,payloadAfter,by omega⟩,frame⟩

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_body_readonly
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_iteration_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_normal

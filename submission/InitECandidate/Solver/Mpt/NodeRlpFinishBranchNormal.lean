import InitECandidate.Solver.Mpt.NodeRlpFinishBranchCost
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real branch phase sums its actual16child results and stored value
size, obtaining a nonwrapping payload<=limit+537 and retaining all nonlocals.
The zero incoming branch payload is to be supplied by the real begin frame. -/
theorem branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (fits : limit+537<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source branchChoice=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ payload.toNat≤limit+537) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "i" (.const 0#64) 0#64 (.seq scanLoop afterScan) rfl (selected.symm.trans normal)
  let entered:=bind source "i" 0#64
  obtain ⟨current,scanRun,valueRun⟩:=Input.sequence_none entered inner scanLoop afterScan continued
  obtain ⟨⟨accumulated,partialCell,partialBound⟩,scanFrame⟩:=scan_normal entered current 0#64 installed (bind_lookup_same _ _ _)
    ((bind_lookup_other source "i" "payload" 0#64 (by decide)).trans payloadCell) (by decide) scanRun
  have memory:=Input.LocalEffects.memory_of_erase entered current scanFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs scanFrame
  have codes:=Input.LocalEffects.code_of_erase entered current scanFrame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  have saved:=(Input.LocalPrefix.loop scanTest scan_body_safe).summary_full entered
  unfold Input.LocalSummary at saved
  rw [←scan_shapes.1,scanRun] at saved
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=
    (saved.1 rfl).trans ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell)
  have currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 160#64 168#64 limit domain (congrFun memory _) (congrFun memory _)
  rw [after_scan_shape] at valueRun
  obtain ⟨funded,values,body,callee,shape,built,returned,assigned,args,called,run,checked,assignRun,valueEnd⟩:=Input.CallNormal.scoped_none_data current inner "vl2" .one (ofString "rlp_value_encoded_len") valueArguments addValue valueRun
  let ready:=Input.CallNormal.continuationEntry current built "vl2" returned
  have reached : Input.CallPrefix.Reaches current (.scoped (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments) ready:=
    .scoped current _ _ _ _ values body callee shape returned built args called (by omega) run checked
  obtain ⟨encoded,_lower,upper,number,lengthCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal (ofString "vl2") valueArguments currentView.pointer currentView.length
    (by have size:=currentView.payload.1; omega) currentInstalled (value_arguments current node limit property currentView currentNode) reached
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word accumulated)):=
    (kept (ofString "payload") (by decide)).trans partialCell
  have read : eval ready (.op .add [localVar "payload",localVar "vl2"])=some (.val (.word (accumulated+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assignedEq:=Input.assign_none ready assigned "payload" (.op .add [localVar "payload",localVar "vl2"]) (accumulated+BitVec.ofNat 64 encoded) read assignRun
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,valueEnd,assignedEq]; rfl
  have payloadNumber : (accumulated+BitVec.ofNat 64 encoded).toNat=accumulated.toNat+encoded:=by
    rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; change accumulated.toNat≤528 at partialBound; omega),number]
  refine ⟨⟨accumulated+BitVec.ofNat 64 encoded,?_,?_⟩,finalFrame.trans (valueFrame.trans scanFrame)⟩
  · rw [endpoint,valueEnd,restore_lookup_other source (restore current "vl2" assigned) "i" "payload" (by decide),restore_lookup_other current assigned "vl2" "payload" (by decide),assignedEq]
    exact bind_lookup_same _ _ _
  · rw [payloadNumber]
    have size:=currentView.payload.1
    change accumulated.toNat≤528 at partialBound
    omega

/-- The real branch preparation returns precisely its sixteen child
references plus its exact encoded value size, retaining the incoming memory. -/
theorem branch_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (data : ReferenceScanData source node) (first : BitVec 64)
    (firstRead : view.length=1#64→eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (fits : limit+537<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source branchChoice=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      payload.toNat=data.total 16+Input.RlpLength.BytesSize.encodedLength first view.length ∧ payload.toNat≤limit+537) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "i" (.const 0#64) 0#64 (.seq scanLoop afterScan) rfl (selected.symm.trans normal)
  let entered:=bind source "i" 0#64
  obtain ⟨current,scanRun,valueRun⟩:=Input.sequence_none entered inner scanLoop afterScan continued
  obtain ⟨⟨accumulated,partialCell,partialExact⟩,_finalIndex,scanFrame⟩:=scan_normal_exact entered current node 0#64 (data.of_frame rfl) installed
    ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell) (bind_lookup_same _ _ _)
    ((bind_lookup_other source "i" "payload" 0#64 (by decide)).trans payloadCell) (by decide) scanRun
  change accumulated.toNat=0+data.total 16 at partialExact
  have totalBound:=data.total_bound 16
  have partialBound : accumulated.toNat≤528:=by omega
  have memory:=Input.LocalEffects.memory_of_erase entered current scanFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs scanFrame
  have codes:=Input.LocalEffects.code_of_erase entered current scanFrame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  have saved:=(Input.LocalPrefix.loop scanTest scan_body_safe).summary_full entered
  unfold Input.LocalSummary at saved
  rw [←scan_shapes.1,scanRun] at saved
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=
    (saved.1 rfl).trans ((bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell)
  let currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 160#64 168#64 limit domain (congrFun memory _) (congrFun memory _)
  have currentFirst : currentView.length=1#64→eval current (.loadByte (.const currentView.pointer))=some (.val (.word first)):=by
    intro one
    change eval current (.loadByte (.const view.pointer))=some (.val (.word first))
    have byte:=firstRead one
    have endian:=congrArg PanSemStateFiniteExact.be scanFrame
    change current.be=source.be at endian
    have currentMemory : current.memory=source.memory:=memory
    have currentDomain : current.memaddrs=source.memaddrs:=domain
    simp only [eval,evalHOLExact,toExact,currentMemory,currentDomain,endian] at byte ⊢
    convert byte using 1 <;> congr 2 <;> apply Subsingleton.elim
  rw [after_scan_shape] at valueRun
  obtain ⟨funded,values,body,callee,shape,built,returned,assigned,args,called,run,checked,assignRun,valueEnd⟩:=Input.CallNormal.scoped_none_data current inner "vl2" .one (ofString "rlp_value_encoded_len") valueArguments addValue valueRun
  let ready:=Input.CallNormal.continuationEntry current built "vl2" returned
  have reached : Input.CallPrefix.Reaches current (.scoped (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments) ready:=
    .scoped current _ _ _ _ values body callee shape returned built args called (by omega) run checked
  obtain ⟨encoded,exactEncoded,_lower,upper,number,lengthCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal_exact (ofString "vl2") valueArguments currentView.pointer currentView.length first
    (by have size:=currentView.payload.1; omega) currentInstalled (value_arguments current node limit property currentView currentNode) currentFirst reached
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word accumulated)):=
    (kept (ofString "payload") (by decide)).trans partialCell
  have read : eval ready (.op .add [localVar "payload",localVar "vl2"])=some (.val (.word (accumulated+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assignedEq:=Input.assign_none ready assigned "payload" (.op .add [localVar "payload",localVar "vl2"]) (accumulated+BitVec.ofNat 64 encoded) read assignRun
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,valueEnd,assignedEq]; rfl
  have payloadNumber : (accumulated+BitVec.ofNat 64 encoded).toNat=accumulated.toNat+encoded:=by
    rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; omega),number]
  refine ⟨⟨accumulated+BitVec.ofNat 64 encoded,?_,?_,?_⟩,finalFrame.trans (valueFrame.trans scanFrame)⟩
  · rw [endpoint,valueEnd,restore_lookup_other source (restore current "vl2" assigned) "i" "payload" (by decide),restore_lookup_other current assigned "vl2" "payload" (by decide),assignedEq]
    exact bind_lookup_same _ _ _
  · rw [payloadNumber,partialExact,exactEncoded]
    simp only [currentView,TrieWalk.ValueView.of_agreement,Nat.zero_add]
  · rw [payloadNumber]
    have size:=currentView.payload.1
    omega

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_normal_exact

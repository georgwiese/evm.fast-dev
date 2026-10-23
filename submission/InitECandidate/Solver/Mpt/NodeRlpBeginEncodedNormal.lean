import InitECandidate.Solver.Mpt.NodeRlpBeginEncoded
import InitECandidate.Solver.Input.ScopedCallNoneData
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual path-size assignment plus optional leaf-value call derives
the final payload word and proves its addition cannot wrap. The source
value view is needed only when the actual current tag selects that call. -/
theorem after_encoded_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag encoded : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (view : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (fits : encoded.toNat+limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (encodedCell : source.locals.lookup (ofString "el")=some (.val (.word encoded)))
    (normal : evaluateHOLFiniteState source afterEncoded=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      encoded.toNat≤payload.toNat ∧ payload.toNat≤encoded.toNat+limit+9) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  rw [after_encoded_shapes.1] at normal
  obtain ⟨current,assigned,continued⟩:=Input.sequence_none source target assignPath leafChoice normal
  have read : eval source (localVar "el")=some (.val (.word encoded)):=by simpa only [eval,evalHOLExact,toExact,localVar] using encodedCell
  have currentEq:=Input.assign_none source current "payload" (localVar "el") encoded read assigned
  have currentTag : current.locals.lookup (ofString "k")=some (.val (.word tag)):=by
    rw [currentEq]
    exact (bind_lookup_other source "payload" "k" encoded (by decide)).trans tagCell
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=by
    rw [currentEq]
    exact (bind_lookup_other source "payload" "node" encoded (by decide)).trans nodeCell
  have currentPayload : current.locals.lookup (ofString "payload")=some (.val (.word encoded)):=by
    rw [currentEq]
    exact bind_lookup_same _ _ _
  have currentFrame : Input.LocalEffects.erase current=Input.LocalEffects.erase source:=by rw [currentEq]; rfl
  have selected : evaluateHOLFiniteState current leafChoice=
      if tag=1#64 then evaluateHOLFiniteState current leafValueCall else (none,current):=by
    rw [after_encoded_shapes.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  by_cases leaf : tag=1#64
  · rw [if_pos leaf] at selected
    have actual:=selected.symm.trans continued
    change evaluateHOLFiniteState current (.decCall (ofString "vl") .one (ofString "rlp_value_encoded_len") leafArguments addLeaf)=(none,target) at actual
    obtain ⟨funded,values,body,callee,shape,built,returned,assignedTarget,args,called,run,checked,assignRun,endpoint⟩:=
      Input.CallNormal.scoped_none_data current target "vl" .one (ofString "rlp_value_encoded_len") leafArguments addLeaf actual
    let ready:=Input.CallNormal.continuationEntry current built "vl" returned
    have reached : Input.CallPrefix.Reaches current (.scoped (ofString "vl") .one (ofString "rlp_value_encoded_len") leafArguments) ready:=
      .scoped current _ _ _ _ values body callee shape returned built args called (by omega) run checked
    have currentView : TrieWalk.ValueView current.memory current.memaddrs node 48#64 56#64 limit property:=by rw [currentEq]; exact view leaf
    have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [currentEq]; exact installed
    obtain ⟨valueLength,lower,upper,number,valueCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal (ofString "vl") leafArguments currentView.pointer currentView.length
      (by have size:=currentView.payload.1; omega) currentInstalled (leaf_arguments current node limit property currentView currentNode) reached
    have savedPayload : ready.locals.lookup (ofString "payload")=some (.val (.word encoded)):=
      (kept (ofString "payload") (by decide)).trans currentPayload
    have addRead : eval ready (.op .add [localVar "payload",localVar "vl"])=some (.val (.word (encoded+BitVec.ofNat 64 valueLength))):=by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,savedPayload,valueCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have assignedEq:=Input.assign_none ready assignedTarget "payload" (.op .add [localVar "payload",localVar "vl"]) (encoded+BitVec.ofNat 64 valueLength) addRead assignRun
    have sumNumber : (encoded+BitVec.ofNat 64 valueLength).toNat=encoded.toNat+valueLength:=by
      rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; omega),number]
    have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,assignedEq]; rfl
    refine ⟨⟨encoded+BitVec.ofNat 64 valueLength,?_,?_,?_⟩,finalFrame.trans (valueFrame.trans currentFrame)⟩
    · rw [endpoint,restore_lookup_other current assignedTarget "vl" "payload" (by decide),assignedEq]
      exact bind_lookup_same _ _ _
    · rw [sumNumber]; omega
    · rw [sumNumber]; have size:=currentView.payload.1; omega
  · rw [if_neg leaf] at selected
    have same : target=current:=congrArg Prod.snd (continued.symm.trans selected)
    rw [same]
    exact ⟨⟨encoded,currentPayload,Nat.le_refl _,by omega⟩,currentFrame⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_normal

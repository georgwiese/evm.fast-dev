import InitECandidate.Solver.Mpt.NodeRlpBeginLengthCost

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual el scope derives a bounded payload and retains all
nonlocals. Both the path-size helper result and optional leaf-value result
come from their real calls, with no future normal result in the model. -/
theorem length_scope_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer length : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (view : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (fits : length.toNat+limit+18<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) buffer))
    (normal : evaluateHOLFiniteState source lengthScope=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      length.toNat≤payload.toNat ∧ payload.toNat≤length.toNat+limit+18) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  obtain ⟨first,argsRead⟩:=length_arguments source buffer length bufferCell lengthCell mapped
  rw [path_shapes.2.2.2.2.2] at normal
  obtain ⟨funded,values,body,callee,shape,built,returned,inner,args,called,run,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_none_data source target "el" .one (ofString "rlp_bytes_encoded_len") lengthArguments afterEncoded normal
  let ready:=Input.CallNormal.continuationEntry source built "el" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "el") .one (ofString "rlp_bytes_encoded_len") lengthArguments) ready:=
    .scoped source _ _ _ _ values body callee shape returned built args called (by omega) run checked
  obtain ⟨encoded,lower,upper,number,encodedCell,kept,frame,_price⟩:=Input.RlpLength.BytesSize.scoped_normal
    (ofString "el") lengthArguments first length (by omega) installed argsRead reached
  have currentNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=
    (kept (ofString "node") (by decide)).trans nodeCell
  have currentTag : ready.locals.lookup (ofString "k")=some (.val (.word tag)):=
    (kept (ofString "k") (by decide)).trans tagCell
  have memory:=Input.LocalEffects.memory_of_erase source ready frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have codes:=Input.LocalEffects.code_of_erase source ready frame
  have currentView (leaf : tag=1#64) : TrieWalk.ValueView ready.memory ready.memaddrs node 48#64 56#64 limit property:=
    (view leaf).of_agreement source.memory ready.memory source.memaddrs ready.memaddrs node 48#64 56#64 limit domain (congrFun memory _) (congrFun memory _)
  obtain ⟨⟨payload,payloadCell,payloadLower,payloadUpper⟩,tailFrame⟩:=after_encoded_normal ready inner node tag (BitVec.ofNat 64 encoded) limit property currentView
    (by rw [number]; omega) (by rw [codes]; exact installed) currentNode currentTag encodedCell continued
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase inner:=by rw [endpoint]; rfl
  refine ⟨⟨payload,?_,?_,?_⟩,finalFrame.trans (tailFrame.trans frame)⟩
  · rw [endpoint,restore_lookup_other source inner "el" "payload" (by decide)]
    exact payloadCell
  · rw [number] at payloadLower
    omega
  · rw [number] at payloadUpper
    omega

theorem length_scope_safe (key : MlS) (notPayload : key≠ofString "payload") (notEncoded : key≠ofString "el") (notValue : key≠ofString "vl") :
    Input.LocalPrefix key lengthScope := by
  rw [path_shapes.2.2.2.2.2]
  exact .decCall _ _ _ _ notEncoded (after_encoded_safe key notPayload notValue)

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.length_scope_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.length_scope_safe

import InitECandidate.Solver.Mpt.NodeRlpBeginEncoded
import InitECandidate.Solver.Input.ScopedCallNoneData
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact arithmetic supplied by the genuine optional leaf-value size call. -/
def ValuePayload (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag encoded payload : BitVec 64) : Prop :=
  ∃ first : BitVec 64,(tag=1#64 → wordAt source.memory (node+56#64)=1#64 →
      eval source (.loadByte (.const (wordAt source.memory (node+48#64))))=some (.val (.word first))) ∧
    payload.toNat=encoded.toNat+(if tag=1#64 then Input.RlpLength.BytesSize.encodedLength first (wordAt source.memory (node+56#64)) else 0)

/-- The true prepared payload and the byte decisions needed by finish. -/
def PathPayload (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer length payload : BitVec 64) : Prop :=
  ∃ pathFirst valueFirst : BitVec 64,(length=1#64 → eval source (.loadByte (.const buffer))=some (.val (.word pathFirst))) ∧
    (tag=1#64 → wordAt source.memory (node+56#64)=1#64 →
      eval source (.loadByte (.const (wordAt source.memory (node+48#64))))=some (.val (.word valueFirst))) ∧
    payload.toNat=Input.RlpLength.BytesSize.encodedLength pathFirst length+
      (if tag=1#64 then Input.RlpLength.BytesSize.encodedLength valueFirst (wordAt source.memory (node+56#64)) else 0)

theorem sizing_byte_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer first : BitVec 64)
    (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source)
    (read : eval source (.loadByte (.const pointer))=some (.val (.word first))) :
    eval target (.loadByte (.const pointer))=some (.val (.word first)) := by
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  simp only [eval,evalHOLExact,toExact,memory,domain,endian] at read ⊢
  convert read using 1 <;> congr 2 <;> apply Subsingleton.elim

theorem ValuePayload.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node tag encoded payload : BitVec 64}
    (sized : ValuePayload source node tag encoded payload) (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    ValuePayload target node tag encoded payload := by
  obtain ⟨first,read,exactCount⟩:=sized
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  refine ⟨first,?_,by simpa only [memory] using exactCount⟩
  intro leaf one
  have oldOne : wordAt source.memory (node+56#64)=1#64:=by simpa only [memory] using one
  have byte:=sizing_byte_frame source target _ first frame (read leaf oldOne)
  simpa only [memory] using byte

theorem PathPayload.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node tag buffer length payload : BitVec 64}
    (sized : PathPayload source node tag buffer length payload) (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    PathPayload target node tag buffer length payload := by
  obtain ⟨pathFirst,valueFirst,pathRead,valueRead,exactCount⟩:=sized
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  refine ⟨pathFirst,valueFirst,fun one=>sizing_byte_frame source target buffer pathFirst frame (pathRead one),?_,by simpa only [memory] using exactCount⟩
  intro leaf one
  have oldOne : wordAt source.memory (node+56#64)=1#64:=by simpa only [memory] using one
  have byte:=sizing_byte_frame source target _ valueFirst frame (valueRead leaf oldOne)
  simpa only [memory] using byte

/-- Payload ownership derives the byte needed by the one-byte special case. -/
theorem sizing_first_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property) :
    ∃ first : BitVec 64,view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word first)) := by
  by_cases one : view.length=1#64
  · have mapped:=view.payload.2.2 0 (by rw [one]; decide)
    simp only [byteAddress,BitVec.add_zero] at mapped
    cases stored : source.memory (panByteAlignHOL (width:=64) view.pointer) with
    | word word=>
      refine ⟨BitVec.ofNat 64 (panGetByteHOL view.pointer word source.be).toNat,?_⟩
      intro _
      simp [eval,evalHOLExact,toExact,panMemLoadByteHOL,stored,mapped]
  · exact ⟨0#64,fun impossible=>(one impossible).elim⟩

/-- Actual path-size assignment plus optional leaf-value call derives
the final payload word and proves its addition cannot wrap. The source
value view is needed only when the actual current tag selects that call. -/
theorem after_encoded_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag encoded : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (view : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (fits : encoded.toNat+limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (encodedCell : source.locals.lookup (ofString "el")=some (.val (.word encoded)))
    (normal : evaluateHOLFiniteState source afterEncoded=(none,target)) :
    (∃ payload : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      encoded.toNat≤payload.toNat ∧ payload.toNat≤encoded.toNat+limit+9 ∧ ValuePayload target node tag encoded payload) ∧
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
    let currentView:=(view leaf).of_agreement source.memory current.memory source.memaddrs current.memaddrs node 48#64 56#64 limit
      (by rw [currentEq]; rfl) (by rw [currentEq]; rfl) (by rw [currentEq]; rfl)
    obtain ⟨first,firstRead⟩:=sizing_first_read current node limit property currentView
    have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [currentEq]; exact installed
    obtain ⟨valueLength,exactValue,lower,upper,number,valueCell,kept,valueFrame,_price⟩:=ValueEncodedLen.scoped_normal_exact (ofString "vl") leafArguments currentView.pointer currentView.length first
      (by have size:=currentView.payload.1; omega) currentInstalled (leaf_arguments current node limit property currentView currentNode) firstRead reached
    have savedPayload : ready.locals.lookup (ofString "payload")=some (.val (.word encoded)):=
      (kept (ofString "payload") (by decide)).trans currentPayload
    have addRead : eval ready (.op .add [localVar "payload",localVar "vl"])=some (.val (.word (encoded+BitVec.ofNat 64 valueLength))):=by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,savedPayload,valueCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have assignedEq:=Input.assign_none ready assignedTarget "payload" (.op .add [localVar "payload",localVar "vl"]) (encoded+BitVec.ofNat 64 valueLength) addRead assignRun
    have sumNumber : (encoded+BitVec.ofNat 64 valueLength).toNat=encoded.toNat+valueLength:=by
      rw [BitVec.toNat_add_of_lt (by rw [number]; have size:=currentView.payload.1; omega),number]
    have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,assignedEq]; rfl
    have pointerWord : wordAt current.memory (node+48#64)=currentView.pointer:=by simp [wordAt,currentView.pointerStored,MemoryBytes.wordBits]
    have lengthWord : wordAt current.memory (node+56#64)=currentView.length:=by simp [wordAt,currentView.lengthStored,MemoryBytes.wordBits]
    have sized : ValuePayload current node tag encoded (encoded+BitVec.ofNat 64 valueLength):=by
      refine ⟨first,?_,?_⟩
      · intro _ one
        rw [pointerWord]
        exact firstRead (by rwa [lengthWord] at one)
      · rw [sumNumber,if_pos leaf,lengthWord,exactValue]
    refine ⟨⟨encoded+BitVec.ofNat 64 valueLength,?_,?_,?_,sized.of_frame (finalFrame.trans valueFrame)⟩,finalFrame.trans (valueFrame.trans currentFrame)⟩
    · rw [endpoint,restore_lookup_other current assignedTarget "vl" "payload" (by decide),assignedEq]
      exact bind_lookup_same _ _ _
    · rw [sumNumber]; omega
    · rw [sumNumber]; have size:=currentView.payload.1; omega
  · rw [if_neg leaf] at selected
    have same : target=current:=congrArg Prod.snd (continued.symm.trans selected)
    rw [same]
    have sized : ValuePayload current node tag encoded encoded:=
      ⟨0#64,fun impossible _=>(leaf impossible).elim,by rw [if_neg leaf,Nat.add_zero]⟩
    exact ⟨⟨encoded,currentPayload,Nat.le_refl _,by omega,sized⟩,currentFrame⟩

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
  obtain ⟨⟨payload,cell,lower,upper,_exact⟩,frame⟩:=after_encoded_normal_exact source target node tag encoded limit property view fits installed nodeCell tagCell encodedCell normal
  exact ⟨⟨payload,cell,lower,upper⟩,frame⟩


/-- Only the real length/value words and single-byte decision words are
needed to retain the computed payload through later memory effects. -/
def PathPayload.Footprint (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer length : BitVec 64) (query : BitVec 64) : Prop :=
  (tag=1#64 ∧ (query=node+48#64 ∨ query=node+56#64)) ∨
    (length=1#64 ∧ query=panByteAlignHOL (width:=64) buffer) ∨
    (tag=1#64 ∧ wordAt source.memory (node+56#64)=1#64 ∧ query=panByteAlignHOL (width:=64) (wordAt source.memory (node+48#64)))

theorem sizing_byte_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer first : BitVec 64)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : target.memory (panByteAlignHOL (width:=64) pointer)=source.memory (panByteAlignHOL (width:=64) pointer))
    (read : eval source (.loadByte (.const pointer))=some (.val (.word first))) :
    eval target (.loadByte (.const pointer))=some (.val (.word first)) := by
  classical
  have same : @panMemLoadByteHOL 64 _ target.memory target.memaddrs (fun query=>Classical.propDecidable (target.memaddrs query)) target.be pointer=
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be pointer:=by
    dsimp only [panMemLoadByteHOL]
    rw [domain,endian]
    exact congrArg (fun cell : HolWordLab 64=>match cell with
      | .word word=>if source.memaddrs (panByteAlignHOL (width:=64) pointer) then some (panGetByteHOL pointer word source.be) else none) memory
  change Option.map (fun value : UInt8=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 value.toNat)))
    (@panMemLoadByteHOL 64 _ target.memory target.memaddrs (fun query=>Classical.propDecidable (target.memaddrs query)) target.be pointer)=_
  rw [same]
  exact read

/-- A partial physical frame suffices for the exact payload; unrelated
memory, cursor globals and caller locals may change. -/
theorem PathPayload.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node tag buffer length payload : BitVec 64}
    (sized : PathPayload source node tag buffer length payload) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query,PathPayload.Footprint source node tag buffer length query → target.memory query=source.memory query) :
    PathPayload target node tag buffer length payload := by
  obtain ⟨pathFirst,valueFirst,pathRead,valueRead,exactCount⟩:=sized
  have pathByte : length=1#64 → eval target (.loadByte (.const buffer))=some (.val (.word pathFirst)):=by
    intro one
    exact sizing_byte_agreement source target buffer pathFirst domain endian (memory _ (Or.inr (Or.inl ⟨one,rfl⟩))) (pathRead one)
  by_cases leaf : tag=1#64
  · have pointerMemory:=memory (node+48#64) (Or.inl ⟨leaf,Or.inl rfl⟩)
    have lengthMemory:=memory (node+56#64) (Or.inl ⟨leaf,Or.inr rfl⟩)
    have pointerWord:=congrArg MemoryBytes.wordBits pointerMemory
    have lengthWord:=congrArg MemoryBytes.wordBits lengthMemory
    change wordAt target.memory (node+48#64)=wordAt source.memory (node+48#64) at pointerWord
    change wordAt target.memory (node+56#64)=wordAt source.memory (node+56#64) at lengthWord
    refine ⟨pathFirst,valueFirst,pathByte,?_,by simpa only [if_pos leaf,lengthWord] using exactCount⟩
    intro _ one
    rw [pointerWord]
    have oldOne : wordAt source.memory (node+56#64)=1#64:=by rwa [lengthWord] at one
    exact sizing_byte_agreement source target _ valueFirst domain endian (memory _ (Or.inr (Or.inr ⟨leaf,oldOne,rfl⟩))) (valueRead leaf oldOne)
  · exact ⟨pathFirst,valueFirst,pathByte,fun impossible _=>(leaf impossible).elim,by simpa only [if_neg leaf] using exactCount⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.sizing_byte_frame
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.ValuePayload.of_frame
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.PathPayload.of_frame
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.sizing_first_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_normal_exact

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.sizing_byte_agreement
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.PathPayload.of_memory

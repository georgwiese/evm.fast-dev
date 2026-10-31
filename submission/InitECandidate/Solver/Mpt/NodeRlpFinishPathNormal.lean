import InitECandidate.Solver.Mpt.NodeRlpFinishBranchNormal
import InitECandidate.Solver.Mpt.NodeRlpBeginGraph

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The observed allocation/header prefix preserves the exact prepared
payload whenever its real sizing words precede the fresh output buffer. -/
theorem BufferOutput.path_payload {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node tag buffer compact length payload : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (aligned : buffer.toNat%8=0)
    (sized : NodeRlpBegin.PathPayload origin node tag compact length payload)
    (nodeBefore : tag=1#64 → node.toNat+64≤buffer.toNat)
    (pathBefore : compact.toNat+length.toNat≤buffer.toNat)
    (valueBefore : tag=1#64 → (wordAt origin.memory (node+48#64)).toNat+
      (wordAt origin.memory (node+56#64)).toNat≤buffer.toNat) :
    NodeRlpBegin.PathPayload source node tag compact length payload := by
  apply sized.of_memory output.runtime.1 output.runtime.2.1
  intro query required
  apply output.before aligned
  rcases required with ⟨leaf,equal|equal⟩|⟨one,equal⟩|⟨leaf,one,equal⟩
  · have number : (node+48#64).toNat=node.toNat+48:=byteAddress_toNat node 48 (by have small:=buffer.isLt; have before:=nodeBefore leaf; omega)
    rw [equal,number]
    have before:=nodeBefore leaf
    omega
  · have number : (node+56#64).toNat=node.toNat+56:=byteAddress_toNat node 56 (by have small:=buffer.isLt; have before:=nodeBefore leaf; omega)
    rw [equal,number]
    have before:=nodeBefore leaf
    omega
  · have number : length.toNat=1:=by rw [one]; rfl
    rw [equal,AllocatedBytes.aligned_number]
    omega
  · have number : (wordAt origin.memory (node+56#64)).toNat=1:=by rw [one]; rfl
    have before:=valueBefore leaf
    rw [equal,AllocatedBytes.aligned_number]
    omega

/-- Any actual path writer with the exact allocated span can be connected
to the two real cache stores. The header frame, heap and protected memory
all come from that same observed prefix and normal writing execution. -/
theorem BufferOutput.finish_plain {origin source written post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer payload : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header)
    (frame : Input.CurrentRlp.WriteFrame source written buffer (header+payload.toNat))
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0)
    (earlier : ∀ query,keep query → query.toNat<buffer.toNat)
    (nodeCell : written.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : written.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : written.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (header+payload.toNat)))))
    (pointerMapped : origin.memaddrs (node+8#64)) (lengthMapped : origin.memaddrs (node+16#64))
    (nodeBefore : node.toNat+24≤2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState written footer=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ FinishOutput origin post node buffer (header+payload.toNat) keep := by
  let base:=PersistentAlloc.post origin buffer (BitVec.ofNat 64 (header+payload.toNat))
  have prefixFrame : Input.CurrentRlp.WriteFrame base source buffer header:=⟨output.fields,output.memory⟩
  have whole:= (prefixFrame.weaken (by omega : header≤header+payload.toNat)).trans frame
  have runtime : written.memaddrs=origin.memaddrs ∧ written.be=origin.be ∧ written.code=origin.code:=
    ⟨(Input.MemoryMetadata.domain frame.metadata).trans output.runtime.1,
      (Input.MemoryMetadata.endian frame.metadata).trans output.runtime.2.1,
      (Input.MemoryMetadata.code frame.metadata).trans output.runtime.2.2⟩
  have actual:=footer_execute written node buffer (BitVec.ofNat 64 (header+payload.toNat)) nodeCell bufferCell offsetCell
    (by rw [runtime.1]; exact pointerMapped) (by rw [runtime.1]; exact lengthMapped)
  have answer : value=.val (.word 0#64):=by
    have same:=congrArg Prod.fst (normal.symm.trans actual)
    exact PanSemResultExact.returned.inj (Option.some.inj same)
  have endpoint:=congrArg Prod.snd (normal.symm.trans actual)
  dsimp only [Prod.snd] at endpoint
  have fields : Input.MemoryMetadata.erase post=Input.MemoryMetadata.erase written:=by rw [endpoint]; rfl
  have postGlobals:=congrArg PanSemStateFiniteExact.globals fields
  change post.globals=written.globals at postGlobals
  have writeGlobals:=congrArg PanSemStateFiniteExact.globals frame.metadata
  change written.globals=source.globals at writeGlobals
  have metadata : Rlp.Validation.scratchMetadata post=Rlp.Validation.scratchMetadata origin:=by
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) (fields.trans whole.metadata)
    exact same
  have globals : HeapGlobals origin post:=by
    have same:=congrArg PanSemStateFiniteExact.globals (fields.trans whole.metadata)
    change post.globals=base.globals at same
    intro key different
    rw [same]
    exact HeapGlobals.update origin _ key different
  have afterFooter (query : BitVec 64) (pointerAway : query≠node+8#64) (lengthAway : query≠node+16#64) :
      post.memory query=written.memory query:=by
    rw [endpoint]
    exact (if_neg lengthAway).trans (if_neg pointerAway)
  have writtenBefore (query : BitVec 64) (before : query.toNat<buffer.toNat) : written.memory query=origin.memory query:=by
    have away:=CopyGeneral.Away.after_floor buffer query (header+payload.toNat) buffer.toNat aligned (Nat.le_refl _)
      (by have room:=output.room; omega) before
    exact whole.memory query away
  have writtenAbove (query : BitVec 64) (above : 2952790016≤query.toNat) : written.memory query=origin.memory query:=
    whole.memory query (CopyGeneral.Away.before buffer query (header+payload.toNat) 2952790016 (by have room:=output.room; omega) (by decide) above)
  refine ⟨answer,?_,?_,?_,?_,metadata,globals,?_,?_⟩
  · rw [endpoint]
    have distinct : node+8#64≠node+16#64:=GasBudget.offsets_ne node 8#64 16#64 (by decide)
    change StoreWord.put (StoreWord.put written.memory (node+8#64) buffer) (node+16#64) (BitVec.ofNat 64 (header+payload.toNat)) (node+8#64)=.word buffer
    simp [StoreWord.put,distinct]
  · rw [endpoint]
    exact if_pos rfl
  · exact ⟨PersistentAlloc.rounded buffer (BitVec.ofNat 64 (header+payload.toNat)),by rw [postGlobals,writeGlobals]; exact output.heapCell,
      output.heapUpper,output.heapAligned,by have growth:=output.growth; omega⟩
  · exact ⟨(Input.MemoryMetadata.domain fields).trans runtime.1,(Input.MemoryMetadata.endian fields).trans runtime.2.1,
      (Input.MemoryMetadata.code fields).trans runtime.2.2⟩
  · intro query required pointerAway lengthAway
    exact (afterFooter query pointerAway lengthAway).trans (writtenBefore query (earlier query required))
  · intro query above
    have pointerNumber : (node+8#64).toNat=node.toNat+8:=byteAddress_toNat node 8 (by omega)
    have lengthNumber : (node+16#64).toNat=node.toNat+16:=byteAddress_toNat node 16 (by omega)
    have pointerAway : query≠node+8#64:=by intro same; rw [same,pointerNumber] at above; omega
    have lengthAway : query≠node+16#64:=by intro same; rw [same,lengthNumber] at above; omega
    exact (afterFooter query pointerAway lengthAway).trans (writtenAbove query above)


theorem path_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer offset compact length : BitVec 64)
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) pathWriteArguments=
      some [.val (.word (buffer+offset)),.val (.word compact),.val (.word length)] := by
  simp [pathWriteArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,bufferCell,offsetCell,compactCell,lengthCell,
    valueIsWord,valueWord,wordOpHOL,wordOp]

theorem leaf_write_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafWriteArguments=
      some [.val (.word (buffer+offset)),.val (.word view.pointer),.val (.word view.length)] := by
  simp [leafWriteArguments,entryField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,bufferCell,offsetCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,view.pointerMapped,view.pointerStored,view.lengthMapped,view.lengthStored]

/-- All outcomes of the actual leaf value-write and offset-update scope. -/
theorem leaf_write_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (small : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    source.clock-(evaluateHOLFiniteState source leafWriteScope).2.clock≤Input.CopyAny.price view.length.toNat+21 := by
  rw [path_write_shapes.2.2.1]
  exact bytes_update_cost source "w2" leafWriteArguments (buffer+offset) view.pointer view.length installed domain small
    (leaf_write_arguments source node buffer offset limit property view nodeCell bufferCell offsetCell)

/-- The leaf value writer returns the same exact size as its actual earlier
value-size helper and retains the true destination span and caller locals. -/
theorem leaf_write_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset first : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (small : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (firstRead : view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word first)))
    (normal : evaluateHOLFiniteState source leafWriteScope=(none,post)) :
    post.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 (Input.RlpLength.BytesSize.encodedLength first view.length)))) ∧
      Input.CurrentRlp.WriteFrame source post (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first view.length) ∧
      ∀ key : MlS,key≠ofString "off" → post.locals.lookup key=source.locals.lookup key := by
  rw [path_write_shapes.2.2.1] at normal
  exact bytes_update_normal source post "w2" leafWriteArguments (buffer+offset) view.pointer view.length first offset (by decide) installed small
    (leaf_write_arguments source node buffer offset limit property view nodeCell bufferCell offsetCell) offsetCell firstRead normal

/-- Derive the true compact-path write and offset state from the actual
first scoped call, retaining its genuine leaf/extension continuation. -/
theorem path_prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer offset compact length first : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (small : length.toNat+32<2^64)
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (firstRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first)))
    (normal : evaluateHOLFiniteState source pathWriteScope=(none,post)) :
    ∃ current inner,post=restore source "w" inner ∧ evaluateHOLFiniteState current pathSecondChoice=(none,inner) ∧
      current.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 (Input.RlpLength.BytesSize.encodedLength first length)))) ∧
      Input.CurrentRlp.WriteFrame source current (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first length) ∧
      ∀ key : MlS,key≠ofString "off" → key≠ofString "w" → current.locals.lookup key=source.locals.lookup key := by
  rw [path_write_shapes.1] at normal
  obtain ⟨funded,values,actualBody,callee,shape,childTarget,returned,inner,actualArgs,called,run,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_none_data source post "w" .one (ofString "rlp_encode_bytes") pathWriteArguments (.seq (addEncoded "w") pathSecondChoice) normal
  let ready:=Input.CallNormal.continuationEntry source childTarget "w" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "w") .one (ofString "rlp_encode_bytes") pathWriteArguments) ready:=
    .scoped source _ _ _ _ values actualBody callee shape returned childTarget actualArgs called (by omega) run checked
  obtain ⟨encoded,exactCount,_lower,_positive,_upper,_number,resultCell,kept,frame⟩:=
    Input.CurrentRlp.BytesWrite.reached_span_normal_exact source ready (ofString "w") pathWriteArguments (buffer+offset) compact length first installed small
      (path_arguments source buffer offset compact length bufferCell offsetCell compactCell lengthCell) firstRead reached
  obtain ⟨current,assignedRun,secondRun⟩:=Input.sequence_none ready inner (addEncoded "w") pathSecondChoice continued
  have readyOffset : ready.locals.lookup (ofString "off")=some (.val (.word offset)):= (kept _ (by decide)).trans offsetCell
  have read : eval ready (.op .add [localVar "off",localVar "w"])=some (.val (.word (offset+BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyOffset,resultCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assigned:=Input.assign_none ready current "off" (.op .add [localVar "off",localVar "w"]) (offset+BitVec.ofNat 64 encoded) read assignedRun
  refine ⟨current,inner,endpoint,secondRun,?_,?_,?_⟩
  · rw [assigned,←exactCount]
    exact bind_lookup_same _ _ _
  · rw [assigned,←exactCount]
    exact ⟨frame.metadata,frame.memory⟩
  · intro key different notResult
    rw [assigned]
    have binding : (bind ready "off" (offset+BitVec.ofNat 64 encoded)).locals.lookup key=ready.locals.lookup key:=by
      simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
    exact binding.trans (kept key (Ne.symm notResult))

/-- An exact normal write preserves all earlier words below an aligned
output buffer, deriving the necessary no-wrap separation from its span. -/
theorem path_frame_before {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {buffer offset : BitVec 64} {bytes : Nat}
    (frame : Input.CurrentRlp.WriteFrame source post (buffer+offset) bytes) (aligned : buffer.toNat%8=0)
    (fits : buffer.toNat+offset.toNat+bytes<2^64) (query : BitVec 64) (earlier : query.toNat<buffer.toNat) : post.memory query=source.memory query := by
  have number : (buffer+offset).toNat=buffer.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by omega)
  exact frame.memory query (CopyGeneral.Away.after_floor (buffer+offset) query bytes buffer.toNat aligned (by rw [number]; omega) (by rw [number]; omega) earlier)

/-- The same single-byte choice is transported using only its actual
retained backing word, full memory-domain agreement and endian fields. -/
theorem path_byte_read {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {buffer offset pointer first : BitVec 64} {bytes : Nat}
    (frame : Input.CurrentRlp.WriteFrame source post (buffer+offset) bytes) (aligned : buffer.toNat%8=0)
    (fits : buffer.toNat+offset.toNat+bytes<2^64) (earlier : (panByteAlignHOL (width:=64) pointer).toNat<buffer.toNat)
    (read : eval source (.loadByte (.const pointer))=some (.val (.word first))) :
    eval post (.loadByte (.const pointer))=some (.val (.word first)) := by
  classical
  have memory:=path_frame_before frame aligned fits _ earlier
  have domain:=Input.MemoryMetadata.domain frame.metadata
  have endian:=Input.MemoryMetadata.endian frame.metadata
  have same : @panMemLoadByteHOL 64 _ post.memory post.memaddrs (fun query=>Classical.propDecidable (post.memaddrs query)) post.be pointer=
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be pointer:=by
    dsimp only [panMemLoadByteHOL]
    rw [domain,endian]
    exact congrArg (fun cell : HolWordLab 64=>match cell with
      | .word word=>if source.memaddrs (panByteAlignHOL (width:=64) pointer) then some (panGetByteHOL pointer word source.be) else none) memory
  change Option.map (fun value : UInt8=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 value.toNat)))
    (@panMemLoadByteHOL 64 _ post.memory post.memaddrs (fun query=>Classical.propDecidable (post.memaddrs query)) post.be pointer)=_
  rw [same]
  exact read


/-- Both actual leaf writes compose to their exact prepared byte count,
retaining the original value decision, node/buffer locals and full span.
The incoming span is the physical budget to be supplied by real preparation. -/
theorem leaf_path_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset compact length pathFirst valueFirst : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (aligned : buffer.toNat%8=0) (nodeBefore : node.toNat+64≤buffer.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤buffer.toNat)
    (pathRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word pathFirst)))
    (valueRead : view.length=1#64 → eval source (.loadByte (.const view.pointer))=some (.val (.word valueFirst)))
    (inside : buffer.toNat+offset.toNat+Input.RlpLength.BytesSize.encodedLength pathFirst length+
      Input.RlpLength.BytesSize.encodedLength valueFirst view.length≤2952790016)
    (normal : evaluateHOLFiniteState source pathWriteScope=(none,post)) :
    let bytes:=offset.toNat+Input.RlpLength.BytesSize.encodedLength pathFirst length+Input.RlpLength.BytesSize.encodedLength valueFirst view.length
    post.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 bytes))) ∧ Input.CurrentRlp.WriteFrame source post buffer bytes ∧
      post.locals.lookup (ofString "node")=some (.val (.word node)) ∧ post.locals.lookup (ofString "buf")=some (.val (.word buffer)) := by
  let pathBytes:=Input.RlpLength.BytesSize.encodedLength pathFirst length
  let valueBytes:=Input.RlpLength.BytesSize.encodedLength valueFirst view.length
  let bytes:=offset.toNat+pathBytes+valueBytes
  let nextOffset:=offset+BitVec.ofNat 64 pathBytes
  obtain ⟨current,inner,endpoint,secondRun,currentOffset,firstFrame,kept⟩:=path_prefix_normal source post buffer offset compact length pathFirst installed pathSmall
    bufferCell offsetCell compactCell lengthCell pathRead normal
  have firstFits : buffer.toNat+offset.toNat+pathBytes<2^64:=by omega
  have currentMemory : ∀ query,query.toNat<buffer.toNat → current.memory query=source.memory query:=path_frame_before firstFrame aligned firstFits
  have pointerNumber : (node+48#64).toNat=node.toNat+48:=byteAddress_toNat node 48 (by have small:=buffer.isLt; omega)
  have lengthNumber : (node+56#64).toNat=node.toNat+56:=byteAddress_toNat node 56 (by have small:=buffer.isLt; omega)
  let currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 48#64 56#64 limit
    (Input.MemoryMetadata.domain firstFrame.metadata) (currentMemory _ (by rw [pointerNumber]; omega)) (currentMemory _ (by rw [lengthNumber]; omega))
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):= (kept _ (by decide) (by decide)).trans nodeCell
  have currentBuffer : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):= (kept _ (by decide) (by decide)).trans bufferCell
  have currentTag : current.locals.lookup (ofString "k")=some (.val (.word 1#64)):= (kept _ (by decide) (by decide)).trans tagCell
  have selected : evaluateHOLFiniteState current pathSecondChoice=evaluateHOLFiniteState current leafWriteScope:=by
    rw [path_write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected] at secondRun
  have currentFirst : currentView.length=1#64 → eval current (.loadByte (.const currentView.pointer))=some (.val (.word valueFirst)):=by
    intro one
    have byteBefore : (panByteAlignHOL (width:=64) view.pointer).toNat<buffer.toNat:=by
      have lengthOne : view.length.toNat=1:=by rw [show view.length=1#64 from one]; rfl
      rw [AllocatedBytes.aligned_number]
      omega
    exact path_byte_read firstFrame aligned firstFits byteBefore (valueRead one)
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [Input.MemoryMetadata.code firstFrame.metadata]; exact installed
  obtain ⟨finalOffset,secondFrame,secondLocals⟩:=leaf_write_normal current inner node buffer nextOffset valueFirst limit property currentView currentInstalled valueSmall
    currentNode currentBuffer currentOffset currentFirst secondRun
  have firstSpan : Input.CurrentRlp.WriteFrame source current (buffer+BitVec.ofNat 64 offset.toNat) pathBytes:=by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using firstFrame
  have secondSpan : Input.CurrentRlp.WriteFrame current inner (buffer+BitVec.ofNat 64 (offset.toNat+pathBytes)) valueBytes:=by
    simpa only [nextOffset,currentView,TrieWalk.ValueView.of_agreement,valueBytes,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using secondFrame
  have whole:= (firstSpan.shift buffer offset.toNat pathBytes bytes (by dsimp only [bytes]; omega)).trans
    (secondSpan.shift buffer (offset.toNat+pathBytes) valueBytes bytes (Nat.le_refl _))
  have offsetEq : nextOffset+BitVec.ofNat 64 valueBytes=BitVec.ofNat 64 bytes:=by
    simp only [nextOffset,bytes,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine ⟨?_,?_,?_,?_⟩
  · rw [endpoint,restore_lookup_other source inner "w" "off" (by decide)]
    rw [←offsetEq]
    exact finalOffset
  · rw [endpoint]
    exact ⟨whole.metadata,whole.memory⟩
  · rw [endpoint,restore_lookup_other source inner "w" "node" (by decide)]
    exact (secondLocals _ (by decide)).trans currentNode
  · rw [endpoint,restore_lookup_other source inner "w" "buf" (by decide)]
    exact (secondLocals _ (by decide)).trans currentBuffer


/-- The actual leaf continuation obtains its current value fields only
from the observed first write's older-memory frame. -/
theorem leaf_after_compact_cost (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset nextOffset : BitVec 64) (written limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (frame : Input.CurrentRlp.WriteFrame source current (buffer+offset) written) (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (small : view.length.toNat+32<2^64)
    (aligned : buffer.toNat%8=0) (fits : buffer.toNat+offset.toNat+written<2^64) (nodeBefore : node.toNat+64≤buffer.toNat)
    (nodeCell : current.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : current.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (bufferCell : current.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : current.locals.lookup (ofString "off")=some (.val (.word nextOffset))) :
    current.clock-(evaluateHOLFiniteState current pathSecondChoice).2.clock≤Input.CopyAny.price view.length.toNat+21 := by
  have memory : ∀ query,query.toNat<buffer.toNat → current.memory query=source.memory query:=path_frame_before frame aligned fits
  have pointerNumber : (node+48#64).toNat=node.toNat+48:=byteAddress_toNat node 48 (by have cap:=buffer.isLt; omega)
  have lengthNumber : (node+56#64).toNat=node.toNat+56:=byteAddress_toNat node 56 (by have cap:=buffer.isLt; omega)
  let currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 48#64 56#64 limit
    (Input.MemoryMetadata.domain frame.metadata) (memory _ (by rw [pointerNumber]; omega)) (memory _ (by rw [lengthNumber]; omega))
  have selected : evaluateHOLFiniteState current pathSecondChoice=evaluateHOLFiniteState current leafWriteScope:=by
    rw [path_write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected]
  exact leaf_write_cost current node buffer nextOffset limit property currentView
    (by rw [Input.MemoryMetadata.code frame.metadata]; exact installed) ((Input.MemoryMetadata.domain frame.metadata).trans domain) small nodeCell bufferCell offsetCell

/-- All outcomes of both genuine leaf path/value writes have a finite
combined allowance, with later value facts derived only on real child returns. -/
theorem leaf_path_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset compact length first : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (aligned : buffer.toNat%8=0) (nodeBefore : node.toNat+64≤buffer.toNat)
    (fits : buffer.toNat+offset.toNat+Input.RlpLength.BytesSize.encodedLength first length<2^64)
    (firstRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first))) :
    source.clock-(evaluateHOLFiniteState source pathWriteScope).2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+42 := by
  obtain ⟨callee,called,d,s,n⟩:=Input.RlpWrite.BytesWrite.environment source.code.lookup (buffer+offset) compact length
    (Input.CurrentRlp.BytesWrite.original_code source.code installed)
  have child:=Input.CurrentRlp.BytesWrite.body_known_length_cost (callEntryStateHOLFinite source callee) (buffer+offset) compact length.toNat pathSmall installed domain d s
    (by change callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))); simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using n)
  rw [path_write_shapes.1]
  have price:=Input.ClockCost.scoped_reached_current source "w" .one (ofString "rlp_encode_bytes") pathWriteArguments _ Input.CurrentRlp.BytesWrite.body
    (.seq (addEncoded "w") pathSecondChoice) callee .one (Input.CopyAny.price length.toNat+20) (Input.CopyAny.price view.length.toNat+21)
    (path_arguments source buffer offset compact length bufferCell offsetCell compactCell lengthCell) called child (by
      intro target returned run _checked
      have byteRead : length=1#64 → eval (callEntryStateHOLFinite source callee) (.loadByte (localVar "src"))=some (.val (.word first)):=by
        intro one
        have byte:=firstRead one
        simp only [eval,evalHOLExact,toExact,localVar,callEntryStateHOLFinite,s] at byte ⊢
        convert byte using 1 <;> congr 2 <;> apply Subsingleton.elim
      obtain ⟨encoded,exactCount,_low,_positive,_high,_number,answer,byteFrame⟩:=Input.CurrentRlp.BytesWrite.body_span_normal_exact
        (callEntryStateHOLFinite source callee) target (buffer+offset) compact length first installed d s n pathSmall byteRead returned run
      let ready:=Input.CallNormal.continuationEntry source target "w" returned
      have callerFrame : Input.CurrentRlp.WriteFrame source ready (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first length):=by
        rw [←exactCount]
        exact ⟨byteFrame.metadata,byteFrame.memory⟩
      have readyOffset : ready.locals.lookup (ofString "off")=some (.val (.word offset)):=
        (Input.CallNormal.continuation_lookup_other source target "w" "off" returned (by decide)).trans offsetCell
      have resultCell : ready.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=
        (Input.CallNormal.continuation_lookup_same source target "w" returned).trans (congrArg some answer)
      have tailPrice:=Input.ClockCost.sequence_reached_current ready (addEncoded "w") pathSecondChoice 0 (Input.CopyAny.price view.length.toNat+21)
        (Input.ClockCost.assign ready.code _ _ ready rfl) (by
          intro current assignedRun
          have read : eval ready (.op .add [localVar "off",localVar "w"])=some (.val (.word (offset+BitVec.ofNat 64 encoded))):=by
            simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyOffset,resultCell,valueIsWord,valueWord,wordOpHOL,wordOp]
          have assigned:=Input.assign_none ready current "off" (.op .add [localVar "off",localVar "w"]) (offset+BitVec.ofNat 64 encoded) read assignedRun
          have currentFrame : Input.CurrentRlp.WriteFrame source current (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first length):=by
            rw [assigned]
            exact ⟨callerFrame.metadata,callerFrame.memory⟩
          have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=by
            rw [assigned]
            exact (bind_lookup_other ready "off" "node" _ (by decide)).trans ((Input.CallNormal.continuation_lookup_other source target "w" "node" returned (by decide)).trans nodeCell)
          have currentBuffer : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):=by
            rw [assigned]
            exact (bind_lookup_other ready "off" "buf" _ (by decide)).trans ((Input.CallNormal.continuation_lookup_other source target "w" "buf" returned (by decide)).trans bufferCell)
          have currentTag : current.locals.lookup (ofString "k")=some (.val (.word 1#64)):=by
            rw [assigned]
            exact (bind_lookup_other ready "off" "k" _ (by decide)).trans ((Input.CallNormal.continuation_lookup_other source target "w" "k" returned (by decide)).trans tagCell)
          have currentOffset : current.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 encoded))):=by rw [assigned]; exact bind_lookup_same _ _ _
          exact leaf_after_compact_cost source current node buffer offset (offset+BitVec.ofNat 64 encoded) _ limit property view currentFrame installed domain valueSmall
            aligned fits nodeBefore currentNode currentTag currentBuffer currentOffset)
      change ready.clock-(evaluateHOLFiniteState ready (.seq (addEncoded "w") pathSecondChoice)).2.clock≤Input.CopyAny.price view.length.toNat+21
      simpa only [Nat.zero_add] using tailPrice)
  omega


/-- The real path-writing scopes cannot escape with a caller return. -/
theorem path_write_safe : Input.LocalPrefix (ofString "node") pathWriteScope := by
  rw [path_write_shapes.1]
  apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
  apply Input.LocalPrefix.seq
  · exact .assign _ _ (by decide)
  · rw [path_write_shapes.2.1]
    apply Input.LocalPrefix.ite
    · rw [path_write_shapes.2.2.1,bytesStep]
      exact .decCall _ _ _ _ (by decide) (.assign _ _ (by decide))
    · rw [path_write_shapes.2.2.2]
      exact .decCall _ _ _ _ (by decide) (.assign _ _ (by decide))

/-- Genuine leaf preparation size, observed buffer allocation and both
real byte writers compose with the literal cache footer. -/
theorem BufferOutput.leaf_writer_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer compact length payload : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header)
    (sized : NodeRlpBegin.PathPayload origin node 1#64 compact length payload)
    (keep : BitVec 64 → Prop) (aligned : buffer.toNat%8=0)
    (earlier : ∀ query,keep query → query.toNat<buffer.toNat)
    (installed : Input.OriginalCode.Installed origin.code)
    (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : origin.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (compactCell : origin.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : origin.locals.lookup (ofString "clen")=some (.val (.word length)))
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64)
    (nodeBefore : node.toNat+64≤buffer.toNat) (pathBefore : compact.toNat+length.toNat≤buffer.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤buffer.toNat)
    (pointerMapped : origin.memaddrs (node+8#64)) (lengthMapped : origin.memaddrs (node+16#64))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source writerTail=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ FinishOutput origin post node buffer (header+payload.toNat) keep := by
  have pointerNumber : (node+48#64).toNat=node.toNat+48:=byteAddress_toNat node 48 (by have small:=buffer.isLt; omega)
  have lengthNumber : (node+56#64).toNat=node.toNat+56:=byteAddress_toNat node 56 (by have small:=buffer.isLt; omega)
  let currentView:=view.of_agreement origin.memory source.memory origin.memaddrs source.memaddrs node 48#64 56#64 limit output.runtime.1
    (output.before aligned _ (by rw [pointerNumber]; omega)) (output.before aligned _ (by rw [lengthNumber]; omega))
  have pointerWord : wordAt origin.memory (node+48#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
  have lengthWord : wordAt origin.memory (node+56#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
  have currentSized:=output.path_payload aligned sized (fun _=>nodeBefore) pathBefore
    (by intro _; rw [pointerWord,lengthWord]; exact valueBefore)
  obtain ⟨pathFirst,valueFirst,pathRead,valueRead,exactCount⟩:=currentSized
  have currentLengthWord : wordAt source.memory (node+56#64)=currentView.length:=by simp [wordAt,currentView.lengthStored,MemoryBytes.wordBits]
  have currentPointerWord : wordAt source.memory (node+48#64)=currentView.pointer:=by simp [wordAt,currentView.pointerStored,MemoryBytes.wordBits]
  have exactPayload : payload.toNat=Input.RlpLength.BytesSize.encodedLength pathFirst length+
      Input.RlpLength.BytesSize.encodedLength valueFirst currentView.length:=by
    simpa [currentLengthWord] using exactCount
  have firstValue : currentView.length=1#64 → eval source (.loadByte (.const currentView.pointer))=some (.val (.word valueFirst)):=by
    intro one
    have read:=valueRead rfl (by rwa [currentLengthWord])
    simpa only [currentPointerWord] using read
  have currentNode : source.locals.lookup (ofString "node")=some (.val (.word node)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans nodeCell
  have currentTag : source.locals.lookup (ofString "k")=some (.val (.word 1#64)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans tagCell
  have currentCompact : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans compactCell
  have currentLength : source.locals.lookup (ofString "clen")=some (.val (.word length)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans lengthCell
  have selected : evaluateHOLFiniteState source writeChoice=evaluateHOLFiniteState source pathWriteScope:=by
    rw [write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have shaped : evaluateHOLFiniteState source (.seq pathWriteScope footer)=(some (.returned value),post):=by
    rw [write_shapes.1,evaluateHOLFiniteState_seq_line780,selected] at normal
    rw [evaluateHOLFiniteState_seq_line780]
    exact normal
  obtain ⟨written,pathRun,footerRun⟩:=Input.sequence_returned source post pathWriteScope footer value (path_write_safe.summary_full source).2.1 shaped
  have offsetNumber : (BitVec.ofNat 64 header).toNat=header:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=output.headerUpper; omega)]
  have room:=output.room
  have spanExact : (BitVec.ofNat 64 header).toNat+Input.RlpLength.BytesSize.encodedLength pathFirst length+
      Input.RlpLength.BytesSize.encodedLength valueFirst currentView.length=header+payload.toNat:=by rw [offsetNumber,exactPayload]; omega
  obtain ⟨offset,frame,writtenNode,writtenBuffer⟩:=leaf_path_normal source written node buffer (BitVec.ofNat 64 header) compact length pathFirst valueFirst limit property currentView
    (by rw [output.runtime.2.2]; exact installed) pathSmall valueSmall currentNode currentTag output.bufferCell output.offsetCell currentCompact currentLength
    aligned nodeBefore valueBefore pathRead firstValue (by omega) pathRun
  rw [spanExact] at offset frame
  exact output.finish_plain frame keep aligned earlier writtenNode writtenBuffer offset pointerMapped lengthMapped (by omega) value footerRun


/-- Price every actual leaf writer outcome from the observed buffer prefix;
the genuine prepared size supplies the first write's nonwrapping extent. -/
theorem BufferOutput.leaf_writer_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer compact length payload : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header)
    (sized : NodeRlpBegin.PathPayload origin node 1#64 compact length payload)
    (aligned : buffer.toNat%8=0) (installed : Input.OriginalCode.Installed origin.code) (domain : origin.memaddrs=InitE.ordinaryDomain)
    (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : origin.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (compactCell : origin.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : origin.locals.lookup (ofString "clen")=some (.val (.word length)))
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView origin.memory origin.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64)
    (nodeBefore : node.toNat+64≤buffer.toNat) (pathBefore : compact.toNat+length.toNat≤buffer.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤buffer.toNat) :
    source.clock-(evaluateHOLFiniteState source writerTail).2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+42 := by
  have pointerNumber : (node+48#64).toNat=node.toNat+48:=byteAddress_toNat node 48 (by have small:=buffer.isLt; omega)
  have lengthNumber : (node+56#64).toNat=node.toNat+56:=byteAddress_toNat node 56 (by have small:=buffer.isLt; omega)
  let currentView:=view.of_agreement origin.memory source.memory origin.memaddrs source.memaddrs node 48#64 56#64 limit output.runtime.1
    (output.before aligned _ (by rw [pointerNumber]; omega)) (output.before aligned _ (by rw [lengthNumber]; omega))
  have pointerWord : wordAt origin.memory (node+48#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
  have lengthWord : wordAt origin.memory (node+56#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
  obtain ⟨pathFirst,_valueFirst,pathRead,_valueRead,exactCount⟩:=output.path_payload aligned sized (fun _=>nodeBefore) pathBefore
    (by intro _; rw [pointerWord,lengthWord]; exact valueBefore)
  have currentNode : source.locals.lookup (ofString "node")=some (.val (.word node)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans nodeCell
  have currentTag : source.locals.lookup (ofString "k")=some (.val (.word 1#64)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans tagCell
  have currentCompact : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans compactCell
  have currentLength : source.locals.lookup (ofString "clen")=some (.val (.word length)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans lengthCell
  have selected : evaluateHOLFiniteState source writeChoice=evaluateHOLFiniteState source pathWriteScope:=by
    rw [write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have offsetNumber : (BitVec.ofNat 64 header).toNat=header:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=output.headerUpper; omega)]
  have price:=leaf_path_cost source node buffer (BitVec.ofNat 64 header) compact length pathFirst limit property currentView
    (by rw [output.runtime.2.2]; exact installed) (output.runtime.1.trans domain) pathSmall valueSmall currentNode currentTag output.bufferCell output.offsetCell currentCompact currentLength
    aligned nodeBefore (by have room:=output.room; rw [offsetNumber]; omega) pathRead
  have choicePrice : source.clock-(evaluateHOLFiniteState source writeChoice).2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+42:=by
    rw [selected]
    exact price
  rw [write_shapes.1]
  have total:=Input.ClockCost.sequence_current source writeChoice footer _ 0 choicePrice (footer_cost source.code)
  simpa only [Nat.add_zero] using total

/-- The buffer prefix has no escaping caller return. -/
theorem buffer_safe : Input.LocalPrefix (ofString "node") (Input.CallPrefix.program bufferTrace .skip) := by
  exact .decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"] (by decide)
    (.decCall (ofString "buf") .one (ofString "alloc") allocationArguments (by decide)
      (.seq (.call none (ofString "rlp_encode_list_header") headerArguments (by intro name impossible; cases impossible))
        (.dec (ofString "off") .one (localVar "hl") (by decide) .skip)))

/-- An actual returned allocation scope has genuinely reached its writer,
regardless of whether its initial clock exceeds a conservative price. -/
theorem buffer_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (fits : payload.toNat+9<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source allocationScope=(some (.returned value),post)) :
    ∃ current inner header,Input.CallPrefix.Execution source bufferTrace current ∧ BufferOutput source current heap payload header ∧
      Input.CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current writerTail=(some (.returned value),inner) := by
  rw [buffer_shape.1] at normal
  rcases Input.CallPrefix.classify_frame source bufferTrace with stopped|reached
  · have observed:=congrArg (fun observation=>observation.1.1) (stopped writerTail)
    change (evaluateHOLFiniteState source (Input.CallPrefix.program bufferTrace writerTail)).1=
      (evaluateHOLFiniteState source (Input.CallPrefix.program bufferTrace .skip)).1 at observed
    rw [normal] at observed
    exact ((buffer_safe.summary_full source).2.1 value observed.symm).elim
  · obtain ⟨current,trace⟩:=reached
    let inner:=(evaluateHOLFiniteState current writerTail).2
    have observed:=trace.observe writerTail
    rw [normal] at observed
    have outcome:=congrArg (fun observation=>observation.1.1) observed
    change some (.returned value)=(evaluateHOLFiniteState current writerTail).1 at outcome
    have clock:=congrArg (fun observation=>observation.1.2) observed
    have fields:=congrArg Prod.snd observed
    change post.clock=inner.clock at clock
    change Input.LocalEffects.erase post=Input.LocalEffects.erase inner at fields
    obtain ⟨header,output⟩:=buffer_normal source current heap payload installed payloadCell heapCell heapLower heapUpper fits trace
    exact ⟨current,inner,header,trace,output,⟨clock,fields⟩,Prod.ext outcome.symm rfl⟩

/-- A leaf skips the real branch preparation without modifying its state. -/
theorem leaf_after_extension (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 1#64))) :
    evaluateHOLFiniteState source afterExtension=evaluateHOLFiniteState source allocationScope := by
  have skipped : evaluateHOLFiniteState source branchChoice=(none,source):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [buffer_shape.2,evaluateHOLFiniteState_seq_line780,skipped]

/-- Actual allocation/header/leaf writing/footer on all outcomes. -/
theorem leaf_finish_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap compact length payload : BitVec 64)
    (sized : NodeRlpBegin.PathPayload source node 1#64 compact length payload)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64) (fits : payload.toNat+9<2^64)
    (nodeBefore : node.toNat+64≤heap.toNat) (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source afterExtension).2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+75 := by
  rw [leaf_after_extension source tagCell]
  let result:=evaluateHOLFiniteState source allocationScope
  change source.clock-result.2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+75
  have run : evaluateHOLFiniteState source allocationScope=(result.1,result.2):=rfl
  rcases buffer_trace source result.2 heap payload installed payloadCell heapCell heapLower heapUpper fits result.1 run with stopped|reached
  · omega
  · obtain ⟨current,inner,header,_trace,output,forward,prefixPrice,scope,continued⟩:=reached
    have price:=output.leaf_writer_cost sized aligned installed domain nodeCell tagCell compactCell lengthCell view pathSmall valueSmall nodeBefore pathBefore valueBefore
    rw [continued] at price
    change current.clock-inner.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+42 at price
    have clock:=scope.clock
    change result.2.clock=inner.clock at clock
    change source.clock-result.2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+75
    omega

/-- Exact begin payload plus the real buffer trace now yields the complete
normal leaf finish phase, including actual allocation and cache stores. -/
theorem leaf_finish_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap compact length payload : BitVec 64)
    (sized : NodeRlpBegin.PathPayload source node 1#64 compact length payload)
    (keep : BitVec 64 → Prop) (earlier : ∀ query,keep query → query.toNat<heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 1#64)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64) (fits : payload.toNat+9<2^64)
    (nodeBefore : node.toNat+64≤heap.toNat) (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat)
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    ∃ header,value=.val (.word 0#64) ∧ header=Input.RlpLength.Header.encodedLength payload ∧
      FinishOutput source post node heap (header+payload.toNat) keep := by
  rw [leaf_after_extension source tagCell] at normal
  obtain ⟨current,inner,header,_trace,output,scope,continued⟩:=buffer_return source post heap payload installed payloadCell heapCell heapLower heapUpper fits value normal
  obtain ⟨answer,finished⟩:=output.leaf_writer_normal sized keep aligned earlier installed nodeCell tagCell compactCell lengthCell view pathSmall valueSmall nodeBefore pathBefore valueBefore pointerMapped lengthMapped value continued
  exact ⟨header,answer,output.headerExact,finished.reframe rfl scope.metadata⟩


/-- The four real finish entry reads, with descriptors installed by begin
and retained in its actual scratch record. Shared by leaf and extension. -/
structure PreparedEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame node tag compact length payload : BitVec 64) : Prop where
  frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame))
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  headerMapped : source.memaddrs node
  headerStored : source.memory node=.word tag
  payloadMapped : source.memaddrs (frame+40#64)
  payloadStored : source.memory (frame+40#64)=.word payload
  bufferMapped : source.memaddrs (frame+24#64)
  bufferStored : source.memory (frame+24#64)=.word compact
  lengthMapped : source.memaddrs (frame+32#64)
  lengthStored : source.memory (frame+32#64)=.word length

/-- The genuine begin result supplies the actual descriptor mappings and
values used by finish. Its node header survives the real high-frame stores. -/
theorem PreparedEntry.of_begin {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node heap frame : BitVec 64} {lower limit allowance : Nat} {property : BitVec 64 → BitVec 64 → Prop} {value : ValueHOL 64}
    (output : NodeRlpBegin.Output origin source node heap frame limit value allowance)
    (data : NodeRlpBegin.Entry origin node heap lower limit property)
    (frameArena : AllocatedBytes.Arena frame 48) (scratch : 2952790016≤frame.toNat)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    PreparedEntry source frame node (wordAt origin.memory node) output.buffer output.length output.payload := by
  have header:=data.graph.header node data.member data.active
  have before:=(data.graph.footprint_bounds lower heap.toNat data.regions node (.header node data.member data.active)).2
  have memory:=output.before_heap frameArena scratch data.heapUpper node before
  exact ⟨frameCell,nodeCell,by rw [output.domain]; exact header.1,memory.trans header.2,
    by rw [output.domain]; exact output.mapped.2.2,output.payloadStored,
    by rw [output.domain]; exact output.mapped.1,output.bufferStored,
    by rw [output.domain]; exact output.mapped.2.1,output.lengthStored⟩

/-- Later child work need retain only these actual descriptor/header words
for the same real finish entry to remain available. -/
theorem PreparedEntry.of_memory {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame node tag compact length payload : BitVec 64}
    (entry : PreparedEntry origin frame node tag compact length payload)
    (domain : source.memaddrs=origin.memaddrs)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (header : source.memory node=origin.memory node)
    (buffer : source.memory (frame+24#64)=origin.memory (frame+24#64))
    (lengthMemory : source.memory (frame+32#64)=origin.memory (frame+32#64))
    (payloadMemory : source.memory (frame+40#64)=origin.memory (frame+40#64)) :
    PreparedEntry source frame node tag compact length payload := by
  exact ⟨frameCell,nodeCell,by rw [domain]; exact entry.headerMapped,header.trans entry.headerStored,
    by rw [domain]; exact entry.payloadMapped,payloadMemory.trans entry.payloadStored,
    by rw [domain]; exact entry.bufferMapped,buffer.trans entry.bufferStored,
    by rw [domain]; exact entry.lengthMapped,lengthMemory.trans entry.lengthStored⟩


def pathStart (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag compact length payload : BitVec 64) :=
  bind (bind (bind (bind source "k" tag) "payload" payload) "cbuf" compact) "clen" length

theorem path_start_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag compact length payload : BitVec 64) :
    (pathStart source tag compact length payload).locals.lookup (ofString "k")=some (.val (.word tag)) ∧
      (pathStart source tag compact length payload).locals.lookup (ofString "payload")=some (.val (.word payload)) ∧
      (pathStart source tag compact length payload).locals.lookup (ofString "cbuf")=some (.val (.word compact)) ∧
      (pathStart source tag compact length payload).locals.lookup (ofString "clen")=some (.val (.word length)) ∧
      (pathStart source tag compact length payload).locals.lookup (ofString "node")=source.locals.lookup (ofString "node") := by
  simp [pathStart,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem PreparedEntry.execution {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node tag compact length payload : BitVec 64}
    (entry : PreparedEntry source frame node tag compact length payload) :
    Input.CallPrefix.Execution source entryTrace (pathStart source tag compact length payload) := by
  let first:=bind source "k" tag
  let second:=bind first "payload" payload
  let third:=bind second "cbuf" compact
  have firstFrame : first.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other source "k" "fr" tag (by decide)).trans entry.frameCell
  have secondFrame : second.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other first "payload" "fr" payload (by decide)).trans firstFrame
  have thirdFrame : third.locals.lookup (ofString "fr")=some (.val (.word frame)):=
    (bind_lookup_other second "cbuf" "fr" compact (by decide)).trans secondFrame
  have tagRead:=entry_field_read source "node" node 0#64 tag entry.nodeCell (by simpa only [BitVec.add_zero] using entry.headerMapped)
    (by simpa only [BitVec.add_zero] using entry.headerStored)
  have payloadRead:=entry_field_read first "fr" frame 40#64 payload firstFrame entry.payloadMapped entry.payloadStored
  have bufferRead:=entry_field_read second "fr" frame 24#64 compact secondFrame entry.bufferMapped entry.bufferStored
  have lengthRead:=entry_field_read third "fr" frame 32#64 length thirdFrame entry.lengthMapped entry.lengthStored
  exact .step (.declare source _ _ _ _ tagRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.step (.declare first _ _ _ _ payloadRead (by simp [shapeOfHOLExact,shapeEqHOL]))
    (.step (.declare second _ _ _ _ bufferRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.step (.declare third _ _ _ _ lengthRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.done _))))

theorem PreparedEntry.observe {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node tag compact length payload : BitVec 64}
    (entry : PreparedEntry source frame node tag compact length payload) :
    Input.CallPrefix.observe (evaluateHOLFiniteState source body)=
      Input.CallPrefix.observe (evaluateHOLFiniteState (pathStart source tag compact length payload) afterLength) := by
  have observed:=entry.execution.observe afterLength
  rw [←entry_shapes.1] at observed
  exact observed

/-- Actual leaf entry reads and the literal extension test retain the
same observed execution and do not consume a source call/loop tick. -/
theorem PreparedEntry.leaf_observe {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node compact length payload : BitVec 64}
    (entry : PreparedEntry source frame node 1#64 compact length payload) :
    Input.CallPrefix.observe (evaluateHOLFiniteState source body)=
      Input.CallPrefix.observe (evaluateHOLFiniteState (pathStart source 1#64 compact length payload) afterExtension) := by
  let current:=pathStart source 1#64 compact length payload
  have tagCell:= (path_start_cells source 1#64 compact length payload).1
  have skipped : evaluateHOLFiniteState current extensionChoice=(none,current):=by
    rw [entry_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip,current]
  have observed:=entry.observe
  rw [entry_shapes.2.1,evaluateHOLFiniteState_seq_line780,skipped] at observed
  exact observed

/-- Complete unchanged finish body for the actual prepared leaf record,
covering all outcomes with its real compact and value byte counts. -/
theorem body_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap compact length payload : BitVec 64)
    (entry : PreparedEntry source frame node 1#64 compact length payload)
    (sized : NodeRlpBegin.PathPayload source node 1#64 compact length payload)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64) (fits : payload.toNat+9<2^64)
    (nodeBefore : node.toNat+64≤heap.toNat) (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤Input.CopyAny.price length.toNat+Input.CopyAny.price view.length.toNat+75 := by
  let current:=pathStart source 1#64 compact length payload
  have cells:=path_start_cells source 1#64 compact length payload
  have price:=leaf_finish_cost current node heap compact length payload (sized.of_frame rfl) installed domain
    (cells.2.2.2.2.trans entry.nodeCell) cells.1 cells.2.2.1 cells.2.2.2.1 cells.2.1 heapCell heapLower heapUpper aligned
    view pathSmall valueSmall fits nodeBefore pathBefore valueBefore
  have same:=congrArg (fun observed=>observed.1.2) entry.leaf_observe
  change (evaluateHOLFiniteState source body).2.clock=(evaluateHOLFiniteState current afterExtension).2.clock at same
  rw [same]
  exact price

/-- Complete normal leaf finish body, including the true loaded descriptors,
its observed allocation, exact writes, cache stores and lexical restoration. -/
theorem body_leaf_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap compact length payload : BitVec 64)
    (entry : PreparedEntry source frame node 1#64 compact length payload)
    (sized : NodeRlpBegin.PathPayload source node 1#64 compact length payload)
    (keep : BitVec 64 → Prop) (earlier : ∀ query,keep query → query.toNat<heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    {limit : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (pathSmall : length.toNat+32<2^64) (valueSmall : view.length.toNat+32<2^64) (fits : payload.toNat+9<2^64)
    (nodeBefore : node.toNat+64≤heap.toNat) (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat)
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header,value=.val (.word 0#64) ∧ header=Input.RlpLength.Header.encodedLength payload ∧
      FinishOutput source post node heap (header+payload.toNat) keep := by
  let current:=pathStart source 1#64 compact length payload
  let inner:=(evaluateHOLFiniteState current afterExtension).2
  have cells:=path_start_cells source 1#64 compact length payload
  have observed:=entry.leaf_observe
  rw [normal] at observed
  have outcome:=congrArg (fun observation=>observation.1.1) observed
  change some (.returned value)=(evaluateHOLFiniteState current afterExtension).1 at outcome
  have run : evaluateHOLFiniteState current afterExtension=(some (.returned value),inner):=Prod.ext outcome.symm rfl
  have scope:=congrArg Prod.snd observed
  change Input.LocalEffects.erase post=Input.LocalEffects.erase inner at scope
  obtain ⟨header,answer,exactHeader,output⟩:=leaf_finish_normal current inner node heap compact length payload (sized.of_frame rfl) keep earlier installed
    (cells.2.2.2.2.trans entry.nodeCell) cells.1 cells.2.2.1 cells.2.2.2.1 cells.2.1 heapCell heapLower heapUpper aligned
    view pathSmall valueSmall fits nodeBefore pathBefore valueBefore pointerMapped lengthMapped value run
  exact ⟨header,answer,exactHeader,output.reframe rfl scope⟩

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_write_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_write_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_write_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_prefix_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_frame_before
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_byte_read

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_path_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_after_compact_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_path_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.path_payload
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.finish_plain

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_write_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.leaf_writer_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.leaf_writer_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_safe

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_return

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_after_extension

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_finish_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.leaf_finish_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_start_cells

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.PreparedEntry.execution

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.PreparedEntry.observe

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.PreparedEntry.leaf_observe

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_leaf_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_leaf_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.PreparedEntry.of_begin
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.PreparedEntry.of_memory

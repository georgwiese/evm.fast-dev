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
  have writeGlobals:=congrArg PanSemStateFiniteExact.globals frame.metadata
  change written.globals=source.globals at writeGlobals
  have metadata : Rlp.Validation.scratchMetadata written=Rlp.Validation.scratchMetadata origin:=by
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) whole.metadata
    exact same
  have globals : HeapGlobals origin written:=by
    have same:=congrArg PanSemStateFiniteExact.globals whole.metadata
    change written.globals=base.globals at same
    intro key different
    rw [same]
    exact HeapGlobals.update origin _ key different
  have completed : WrittenOutput origin written buffer (header+payload.toNat) keep:=by
    refine ⟨⟨PersistentAlloc.rounded buffer (BitVec.ofNat 64 (header+payload.toNat)),by rw [writeGlobals]; exact output.heapCell,
      output.heapUpper,output.heapAligned,by have growth:=output.growth; omega⟩,runtime,metadata,globals,?_,?_⟩
    · intro query required
      exact whole.memory query (CopyGeneral.Away.after_floor buffer query (header+payload.toNat) buffer.toNat aligned (Nat.le_refl _)
        (by have room:=output.room; omega) (earlier query required))
    · intro query above
      exact whole.memory query (CopyGeneral.Away.before buffer query (header+payload.toNat) 2952790016 (by have room:=output.room; omega) (by decide) above)
  exact completed.footer nodeCell bufferCell offsetCell pointerMapped lengthMapped nodeBefore value normal


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

/-- Price the shared genuine compact-path call and offset update once,
then invoke a continuation bound only at its actual normal returned state. -/
theorem path_write_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset compact length first tag : BitVec 64) (allowance : Nat)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pathSmall : length.toNat+32<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (firstRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first)))
    (next : ∀ current,Input.CurrentRlp.WriteFrame source current (buffer+offset) (Input.RlpLength.BytesSize.encodedLength first length) →
      current.locals.lookup (ofString "node")=some (.val (.word node)) → current.locals.lookup (ofString "k")=some (.val (.word tag)) →
      current.locals.lookup (ofString "buf")=some (.val (.word buffer)) →
      current.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 (Input.RlpLength.BytesSize.encodedLength first length)))) →
      current.clock-(evaluateHOLFiniteState current pathSecondChoice).2.clock≤allowance) :
    source.clock-(evaluateHOLFiniteState source pathWriteScope).2.clock≤Input.CopyAny.price length.toNat+21+allowance := by
  obtain ⟨callee,called,d,s,n⟩:=Input.RlpWrite.BytesWrite.environment source.code.lookup (buffer+offset) compact length
    (Input.CurrentRlp.BytesWrite.original_code source.code installed)
  have child:=Input.CurrentRlp.BytesWrite.body_known_length_cost (callEntryStateHOLFinite source callee) (buffer+offset) compact length.toNat pathSmall installed domain d s
    (by change callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))); simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using n)
  rw [path_write_shapes.1]
  have price:=Input.ClockCost.scoped_reached_current source "w" .one (ofString "rlp_encode_bytes") pathWriteArguments _ Input.CurrentRlp.BytesWrite.body
    (.seq (addEncoded "w") pathSecondChoice) callee .one (Input.CopyAny.price length.toNat+20) allowance
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
      have tailPrice:=Input.ClockCost.sequence_reached_current ready (addEncoded "w") pathSecondChoice 0 allowance
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
          have currentTag : current.locals.lookup (ofString "k")=some (.val (.word tag)):=by
            rw [assigned]
            exact (bind_lookup_other ready "off" "k" _ (by decide)).trans ((Input.CallNormal.continuation_lookup_other source target "w" "k" returned (by decide)).trans tagCell)
          have currentOffset : current.locals.lookup (ofString "off")=some (.val (.word (offset+BitVec.ofNat 64 encoded))):=by rw [assigned]; exact bind_lookup_same _ _ _
          exact next current currentFrame currentNode currentTag currentBuffer (by simpa only [←exactCount] using currentOffset))
      change ready.clock-(evaluateHOLFiniteState ready (.seq (addEncoded "w") pathSecondChoice)).2.clock≤allowance
      simpa only [Nat.zero_add] using tailPrice)
  omega


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
  have price:=path_write_cost source node buffer offset compact length first 1#64 (Input.CopyAny.price view.length.toNat+21)
    installed domain pathSmall nodeCell tagCell bufferCell offsetCell compactCell lengthCell firstRead (by
      intro current frame currentNode currentTag currentBuffer currentOffset
      exact leaf_after_compact_cost source current node buffer offset _ _ limit property view frame installed domain valueSmall aligned fits nodeBefore
        currentNode currentTag currentBuffer currentOffset)
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


/-- The actual extension child slot and current stable reference inputs.
The mutable hash-cache word at child24 is deliberately read afresh later. -/
structure ExtensionData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) where
  child : BitVec 64
  tag : BitVec 64
  cached : BitVec 64
  length : BitVec 64
  slot : source.memaddrs (node+48#64) ∧ source.memory (node+48#64)=.word child
  header : child≠0#64 → source.memaddrs child ∧ source.memory child=.word tag
  cache : child≠0#64 → tag≠0#64 → source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached
  size : child≠0#64 → tag≠0#64 → cached≠0#64 → source.memaddrs (child+16#64) ∧ source.memory (child+16#64)=.word length

def ExtensionData.word {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) : BitVec 64:=NodeRefLen.referenceWord data.child data.tag data.length

def ExtensionData.of_frame {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (frame : Input.LocalEffects.erase current=Input.LocalEffects.erase source) : ExtensionData current node := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change current.memaddrs=source.memaddrs at domain
  have memory:=Input.LocalEffects.memory_of_erase source current frame
  exact {
    child:=data.child,tag:=data.tag,cached:=data.cached,length:=data.length
    slot:=by simpa only [domain,memory] using data.slot
    header:=by simpa only [domain,memory] using data.header
    cache:=by simpa only [domain,memory] using data.cache
    size:=by simpa only [domain,memory] using data.size}

theorem ExtensionData.child_member {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64) : graph.valid data.child := by
  let view:=graph.extension node member active tag
  have same : data.child=view.child:=HolWordLab.word.inj (data.slot.2.symm.trans view.stored)
  rw [same]
  exact view.member

noncomputable def ExtensionData.of_graph (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64) (lower upper : Nat) (regions : graph.Regions lower upper)
    (domain : source.memaddrs=InitE.ordinaryDomain) : ExtensionData source node := by
  let view:=graph.extension node member active tag
  let childTag:=wordAt source.memory view.child
  let cached:=wordAt source.memory (view.child+8#64)
  let length:=if view.child=0#64 ∨ childTag=0#64 ∨ cached=0#64 then 0#64 else wordAt source.memory (view.child+16#64)
  refine ⟨view.child,childTag,cached,length,⟨view.mapped,view.stored⟩,?_,?_,?_⟩
  · intro live
    exact graph.header view.child view.member live
  · intro live _nonHash
    exact ⟨reference_cache_mapped source graph lower upper regions domain view.child view.member live 8 (by decide) (by decide),reference_word_stored source.memory _⟩
  · intro live nonHash populated
    have relevant : ¬(view.child=0#64 ∨ childTag=0#64 ∨ cached=0#64):=by
      rintro (zero|zero|zero)
      · exact live zero
      · exact nonHash zero
      · exact populated zero
    refine ⟨reference_cache_mapped source graph lower upper regions domain view.child view.member live 16 (by decide) (by decide),?_⟩
    simp only [length,if_neg relevant]
    exact reference_word_stored source.memory _

theorem ExtensionData.size_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionSizeArguments=some [.val (.word data.child)] := by
  simp [extensionSizeArguments,entryField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,data.slot.1,data.slot.2]

/-- All outcomes of the genuine extension child-size call and addition. -/
theorem extension_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code extensionScope 2 := by
  rw [extension_shape]
  exact Input.ClockCost.scoped_body code (ofString "rl") .one (ofString "node_ref_len") extensionSizeArguments addExtension
    NodeRefLen.formals NodeRefLen.body .one 1 0 (NodeRefLen.original_code code installed) (NodeRefLen.body_cost code installed)
    (Input.ClockCost.assign code _ _)

/-- A genuine normal extension size call adds its exact child reference,
deriving cache population and the nonwrapping payload from this same run. -/
theorem extension_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node payload : BitVec 64)
    (data : ExtensionData source node) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (fits : payload.toNat+33<2^64) (normal : evaluateHOLFiniteState source extensionScope=(none,target)) :
    target.locals.lookup (ofString "payload")=some (.val (.word (payload+data.word))) ∧
      (payload+data.word).toNat=payload.toNat+data.word.toNat ∧
      (data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧
      (∀ key : MlS,key≠ofString "payload" → target.locals.lookup key=source.locals.lookup key) := by
  rw [extension_shape] at normal
  obtain ⟨funded,values,actualBody,callee,shape,built,returned,inner,args,called,run,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_none_data source target "rl" .one (ofString "node_ref_len") extensionSizeArguments addExtension normal
  let ready:=Input.CallNormal.continuationEntry source built "rl" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "rl") .one (ofString "node_ref_len") extensionSizeArguments) ready:=
    .scoped source _ _ _ _ values actualBody callee shape returned built args called (by omega) run checked
  obtain ⟨lengthCell,populated,kept,frame,_price⟩:=NodeRefLen.scoped_normal_exact (ofString "rl") extensionSizeArguments data.child data.tag data.cached data.length
    installed (data.size_arguments nodeCell) data.header data.cache data.size reached
  have readyPayload : ready.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (kept _ (by decide)).trans payloadCell
  have read : eval ready (.op .add [localVar "payload",localVar "rl"])=some (.val (.word (payload+data.word))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyPayload,lengthCell,ExtensionData.word,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assigned:=Input.assign_none ready inner "payload" (.op .add [localVar "payload",localVar "rl"]) (payload+data.word) read continued
  have resultFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase ready:=by rw [endpoint,assigned]; rfl
  refine ⟨?_,BitVec.toNat_add_of_lt (by have bound:=NodeRefLen.reference_bound data.child data.tag data.length; change data.word.toNat≤33 at bound; omega),populated,resultFrame.trans frame,?_⟩
  · rw [endpoint,restore_lookup_other source inner "rl" "payload" (by decide),assigned]
    exact bind_lookup_same _ _ _
  · intro key different
    by_cases resultKey : key=ofString "rl"
    · subst key
      rw [endpoint]
      change (HolFiniteMapExact.resVarEq inner.locals (ofString "rl",source.locals.lookup (ofString "rl"))).lookup (ofString "rl")=_
      rw [lookup_resVarEq_toExact]
      cases old : source.locals.lookup (ofString "rl") <;> simp [resVarHOLExact,FUPDATE,FDOMSUB,old]
    · rw [endpoint]
      have notResult : ofString "rl"≠key:=Ne.symm resultKey
      have notPayload : ofString "payload"≠key:=Ne.symm different
      have restored : (restore source "rl" inner).locals.lookup key=inner.locals.lookup key:=by
        change (HolFiniteMapExact.resVarEq inner.locals (ofString "rl",source.locals.lookup (ofString "rl"))).lookup key=_
        rw [lookup_resVarEq_toExact]
        cases source.locals.lookup (ofString "rl") <;> simp [resVarHOLExact,FUPDATE,FDOMSUB,resultKey]
      rw [restored]
      rw [assigned]
      have same : (bind ready "payload" (payload+data.word)).locals.lookup key=ready.locals.lookup key:=by
        simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notPayload]
      exact same.trans (kept key notResult)


/-- Precisely the stable reference input words, excluding mutable HASH24. -/
def ExtensionData.Footprint {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (query : BitVec 64) : Prop :=
  query=node+48#64 ∨ (data.child≠0#64 ∧ query=data.child) ∨
    (data.child≠0#64 ∧ data.tag≠0#64 ∧ query=data.child+8#64) ∨
    (data.child≠0#64 ∧ data.tag≠0#64 ∧ data.cached≠0#64 ∧ query=data.child+16#64)

def ExtensionData.of_memory {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (domain : current.memaddrs=source.memaddrs)
    (memory : ∀ query,data.Footprint query → current.memory query=source.memory query) : ExtensionData current node := by
  refine ⟨data.child,data.tag,data.cached,data.length,?_,?_,?_,?_⟩
  · exact ⟨by rw [domain]; exact data.slot.1,(memory _ (Or.inl rfl)).trans data.slot.2⟩
  · intro live
    exact ⟨by rw [domain]; exact (data.header live).1,(memory _ (Or.inr (Or.inl ⟨live,rfl⟩))).trans (data.header live).2⟩
  · intro live nonHash
    exact ⟨by rw [domain]; exact (data.cache live nonHash).1,
      (memory _ (Or.inr (Or.inr (Or.inl ⟨live,nonHash,rfl⟩)))).trans (data.cache live nonHash).2⟩
  · intro live nonHash populated
    exact ⟨by rw [domain]; exact (data.size live nonHash populated).1,
      (memory _ (Or.inr (Or.inr (Or.inr ⟨live,nonHash,populated,rfl⟩)))).trans (data.size live nonHash populated).2⟩

theorem ExtensionData.writer_bytes {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) : NodeWriteRef.referenceBytes data.child data.tag data.length.toNat=data.word.toNat := by
  have same:=NodeWriteRef.reference_word_eq data.child data.tag data.length.toNat data.length.isLt
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at same
  have bound:=NodeWriteRef.reference_bytes_bound data.child data.tag data.length.toNat
  have number : (BitVec.ofNat 64 (NodeWriteRef.referenceBytes data.child data.tag data.length.toNat)).toNat=
      NodeWriteRef.referenceBytes data.child data.tag data.length.toNat:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have native:=congrArg BitVec.toNat same
  rw [number] at native
  exact native.symm

theorem ExtensionData.hash_data {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (heap : BitVec 64) (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (domain : source.memaddrs=InitE.ordinaryDomain) (live : data.child≠0#64) (nonHash : data.tag≠0#64) (populated : data.cached≠0#64) :
    NodeHashCached.Data source data.child heap data.cached data.length.toNat :=
  ⟨installed,(data.cache live nonHash).1,(data.cache live nonHash).2,(data.size live nonHash populated).1,
    by simpa using (data.size live nonHash populated).2,heapCell,heapUpper,data.length.isLt,domain⟩

theorem ExtensionData.writer_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (buffer offset : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionWriteArguments=
      some [.val (.word data.child),.val (.word (buffer+offset))] := by
  simp [extensionWriteArguments,entryField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,bufferCell,offsetCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,data.slot.1,data.slot.2]

/-- Every outcome of the actual extension reference call/off update,
including the real software hash when this child needs one. -/
theorem extension_write_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset heap : BitVec 64)
    (data : ExtensionData source node) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    source.clock-(evaluateHOLFiniteState source extensionWriteScope).2.clock≤CurrentKeccak.Hash.bodyPrice data.length.toNat+47 := by
  obtain ⟨callee,called,childCell,_dstCell⟩:=NodeWriteRef.environment source.code.lookup data.child (buffer+offset) (NodeWriteRef.original_code source.code installed)
  have price:=NodeWriteRef.body_cost (callEntryStateHOLFinite source callee) data.child data.tag heap data.cached data.length.toNat installed childCell data.header data.cache
    (fun live nonHash populated=>(data.hash_data heap installed heapCell heapUpper domain live nonHash populated).of_frame rfl)
  rw [path_write_shapes.2.2.2]
  have result:=Input.ClockCost.scoped_current source (ofString "w3") .one (ofString "node_write_ref") extensionWriteArguments _ NodeWriteRef.body (addEncoded "w3")
    callee .one (CurrentKeccak.Hash.bodyPrice data.length.toNat+46) 0 (data.writer_arguments buffer offset nodeCell bufferCell offsetCell) called price
    (Input.ClockCost.assign source.code _ _)
  simpa only [Nat.add_zero,Nat.add_assoc] using result

/-- The genuine extension reference writer and offset assignment return
exactly the earlier reference size, retaining the actual hash/heap frame. -/
theorem extension_write_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node buffer offset heap cached stp pad : BitVec 64)
    (data : ExtensionData source node) (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (small : data.length.toNat+136<2^64)
    (digest : data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64 → source.memaddrs (data.child+24#64) ∧ source.memory (data.child+24#64)=.word cached)
    (normal : evaluateHOLFiniteState source extensionWriteScope=(none,post)) :
    ∃ output : NodeWriteRef.Output source post data.child (buffer+offset) heap cached stp pad (.val (.word (BitVec.ofNat 64 data.word.toNat))),
      output.bytes=data.word.toNat ∧ (data.child=0#64 → output.hashed=false) ∧
      post.locals.lookup (ofString "off")=some (.val (.word (offset+data.word))) ∧
      post.locals.lookup (ofString "node")=some (.val (.word node)) ∧ post.locals.lookup (ofString "buf")=some (.val (.word buffer)) := by
  rw [path_write_shapes.2.2.2] at normal
  obtain ⟨funded,values,actualBody,callee,shape,built,returned,inner,args,called,run,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_none_data source post "w3" .one (ofString "node_write_ref") extensionWriteArguments (addEncoded "w3") normal
  let ready:=Input.CallNormal.continuationEntry source built "w3" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "w3") .one (ofString "node_write_ref") extensionWriteArguments) ready:=
    .scoped source _ _ _ _ values actualBody callee shape returned built args called (by omega) run checked
  have results:=NodeWriteRef.reached_normal_exact source ready "w3" extensionWriteArguments data.child (buffer+offset) data.tag heap data.cached cached stp pad data.length.toNat
    environment heapLower (data.writer_arguments buffer offset nodeCell bufferCell offsetCell) data.header data.cache
    (fun live nonHash populated=>data.hash_data heap environment.installed heapCell heapUpper environment.domain live nonHash populated) digest reached
  rw [data.writer_bytes] at results
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at results
  obtain ⟨resultCell,output,size,noHash⟩:=results
  have readyOffset : ready.locals.lookup (ofString "off")=some (.val (.word offset)):=
    (Input.CallNormal.continuation_lookup_other source built "w3" "off" returned (by decide)).trans offsetCell
  have read : eval ready (.op .add [localVar "off",localVar "w3"])=some (.val (.word (offset+data.word))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,readyOffset,resultCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have assigned:=Input.assign_none ready inner "off" (.op .add [localVar "off",localVar "w3"]) (offset+data.word) read continued
  have finalFrame : Input.LocalEffects.erase post=Input.LocalEffects.erase ready:=by rw [endpoint,assigned]; rfl
  let lifted:=output.reframe rfl finalFrame
  refine ⟨lifted,size,noHash,?_,?_,?_⟩
  · rw [endpoint,restore_lookup_other source inner "w3" "off" (by decide),assigned]
    exact bind_lookup_same _ _ _
  · rw [endpoint,restore_lookup_other source inner "w3" "node" (by decide),assigned]
    exact (bind_lookup_other ready "off" "node" _ (by decide)).trans
      ((Input.CallNormal.continuation_lookup_other source built "w3" "node" returned (by decide)).trans nodeCell)
  · rw [endpoint,restore_lookup_other source inner "w3" "buf" (by decide),assigned]
    exact (bind_lookup_other ready "off" "buf" _ (by decide)).trans
      ((Input.CallNormal.continuation_lookup_other source built "w3" "buf" returned (by decide)).trans bufferCell)


/-- The actual compact write retains the stable child reference inputs
and heap binding before the real extension reference writer is entered. -/
theorem extension_after_compact_cost (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node buffer offset nextOffset heap : BitVec 64) (bytes : Nat) (data : ExtensionData source node)
    (frame : Input.CurrentRlp.WriteFrame source current (buffer+offset) bytes)
    (installed : Input.OriginalCode.Installed source.code) (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapUpper : heap.toNat≤2952790016) (domain : source.memaddrs=InitE.ordinaryDomain)
    (aligned : buffer.toNat%8=0) (fits : buffer.toNat+offset.toNat+bytes<2^64)
    (before : ∀ query,data.Footprint query → query.toNat<buffer.toNat)
    (nodeCell : current.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : current.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (bufferCell : current.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : current.locals.lookup (ofString "off")=some (.val (.word nextOffset))) :
    current.clock-(evaluateHOLFiniteState current pathSecondChoice).2.clock≤CurrentKeccak.Hash.bodyPrice data.length.toNat+47 := by
  let currentData:=data.of_memory (Input.MemoryMetadata.domain frame.metadata)
    (fun query required=>path_frame_before frame aligned fits query (before query required))
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame.metadata
    exact same.trans heapCell
  have selected : evaluateHOLFiniteState current pathSecondChoice=evaluateHOLFiniteState current extensionWriteScope:=by
    rw [path_write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected]
  exact extension_write_cost current node buffer nextOffset heap currentData (by rw [Input.MemoryMetadata.code frame.metadata]; exact installed)
    nodeCell bufferCell offsetCell currentHeap heapUpper ((Input.MemoryMetadata.domain frame.metadata).trans domain)

/-- All actual outcomes of compact-path and extension reference writing. -/
theorem extension_path_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node buffer offset compact length first heap : BitVec 64) (data : ExtensionData source node)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapUpper : heap.toNat≤2952790016)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (aligned : buffer.toNat%8=0)
    (fits : buffer.toNat+offset.toNat+Input.RlpLength.BytesSize.encodedLength first length<2^64)
    (before : ∀ query,data.Footprint query → query.toNat<buffer.toNat)
    (firstRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first))) :
    source.clock-(evaluateHOLFiniteState source pathWriteScope).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+68 := by
  have price:=path_write_cost source node buffer offset compact length first 2#64 (CurrentKeccak.Hash.bodyPrice data.length.toNat+47)
    installed domain pathSmall nodeCell tagCell bufferCell offsetCell compactCell lengthCell firstRead (by
      intro current frame currentNode currentTag currentBuffer currentOffset
      exact extension_after_compact_cost source current node buffer offset _ heap _ data frame installed heapCell heapUpper domain aligned fits before
        currentNode currentTag currentBuffer currentOffset)
  omega


/-- The real allocated extension writer uses its genuine compact payload
plus the exact reference size supplied by extension preparation. -/
theorem BufferOutput.extension_writer_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer compact length compactPayload payload : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ExtensionData origin node)
    (sized : NodeRlpBegin.PathPayload origin node 2#64 compact length compactPayload)
    (exactPayload : payload.toNat=compactPayload.toNat+data.word.toNat)
    (aligned : buffer.toNat%8=0) (installed : Input.OriginalCode.Installed origin.code) (domain : origin.memaddrs=InitE.ordinaryDomain)
    (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : origin.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (compactCell : origin.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : origin.locals.lookup (ofString "clen")=some (.val (.word length)))
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64)
    (pathBefore : compact.toNat+length.toNat≤buffer.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<buffer.toNat) :
    source.clock-(evaluateHOLFiniteState source writerTail).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+68 := by
  obtain ⟨first,_valueFirst,firstRead,_valueRead,exactCompact⟩:=sized
  have compactExact : compactPayload.toNat=Input.RlpLength.BytesSize.encodedLength first length:=by simpa using exactCompact
  let currentData:=data.of_memory output.runtime.1 (fun query required=>output.before aligned query (before query required))
  have currentFirst : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first)):=by
    intro one
    have number : length.toNat=1:=by rw [one]; rfl
    exact NodeRlpBegin.sizing_byte_agreement origin source compact first output.runtime.1 output.runtime.2.1
      (output.before aligned _ (by rw [AllocatedBytes.aligned_number]; omega)) (firstRead one)
  have currentNode : source.locals.lookup (ofString "node")=some (.val (.word node)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans nodeCell
  have currentTag : source.locals.lookup (ofString "k")=some (.val (.word 2#64)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans tagCell
  have currentCompact : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans compactCell
  have currentLength : source.locals.lookup (ofString "clen")=some (.val (.word length)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans lengthCell
  have offsetNumber : (BitVec.ofNat 64 header).toNat=header:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=output.headerUpper; omega)]
  have selected : evaluateHOLFiniteState source writeChoice=evaluateHOLFiniteState source pathWriteScope:=by
    rw [write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have price:=extension_path_cost source node buffer (BitVec.ofNat 64 header) compact length first
    (PersistentAlloc.rounded buffer (BitVec.ofNat 64 (header+payload.toNat))) currentData
    (by rw [output.runtime.2.2]; exact installed) (output.runtime.1.trans domain) output.heapCell output.heapUpper pathSmall small
    currentNode currentTag output.bufferCell output.offsetCell currentCompact currentLength aligned
    (by rw [offsetNumber]; have room:=output.room; omega) before currentFirst
  have choicePrice : source.clock-(evaluateHOLFiniteState source writeChoice).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+68:=by
    rw [selected]
    exact price
  rw [write_shapes.1]
  have total:=Input.ClockCost.sequence_current source writeChoice footer _ 0 choicePrice (footer_cost source.code)
  simpa only [Nat.add_zero] using total

/-- Any genuine nonbranch tag skips branch preparation in the same state. -/
theorem path_after_extension (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag))) (notBranch : tag≠3#64) :
    evaluateHOLFiniteState source afterExtension=evaluateHOLFiniteState source allocationScope := by
  have skipped : evaluateHOLFiniteState source branchChoice=(none,source):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,notBranch,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [buffer_shape.2,evaluateHOLFiniteState_seq_line780,skipped]

/-- Actual extension allocation/header/path/reference/footer outcomes,
from the true payload after its real child-size addition. -/
theorem extension_buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap compact length compactPayload payload : BitVec 64)
    (data : ExtensionData source node) (sized : NodeRlpBegin.PathPayload source node 2#64 compact length compactPayload)
    (exactPayload : payload.toNat=compactPayload.toNat+data.word.toNat)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64) (fits : payload.toNat+9<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<heap.toNat) :
    source.clock-(evaluateHOLFiniteState source afterExtension).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+101 := by
  rw [path_after_extension source 2#64 tagCell (by decide)]
  let result:=evaluateHOLFiniteState source allocationScope
  change source.clock-result.2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+101
  have run : evaluateHOLFiniteState source allocationScope=(result.1,result.2):=rfl
  rcases buffer_trace source result.2 heap payload installed payloadCell heapCell heapLower heapUpper fits result.1 run with stopped|reached
  · omega
  · obtain ⟨current,inner,header,_trace,output,forward,prefixPrice,scope,continued⟩:=reached
    have price:=output.extension_writer_cost data sized exactPayload aligned installed domain nodeCell tagCell compactCell lengthCell pathSmall small pathBefore before
    rw [continued] at price
    change current.clock-inner.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+68 at price
    have clock:=scope.clock
    change result.2.clock=inner.clock at clock
    omega

/-- Complete extension preparation and finish phase. Physical reference
inputs for every reached writer come from that same real read-only size call. -/
theorem extension_finish_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap compact length payload : BitVec 64)
    (data : ExtensionData source node) (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<heap.toNat) :
    source.clock-(evaluateHOLFiniteState source afterLength).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+103 := by
  have selected : evaluateHOLFiniteState source extensionChoice=evaluateHOLFiniteState source extensionScope:=by
    rw [entry_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have front : source.clock-(evaluateHOLFiniteState source extensionChoice).2.clock≤2:=by
    rw [selected]
    exact extension_cost source.code installed source rfl
  rw [entry_shapes.2.1]
  have price:=Input.ClockCost.sequence_reached_current source extensionChoice afterExtension 2
    (Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+101) front (by
      intro current normal
      rw [selected] at normal
      obtain ⟨payloadAfter,number,_populated,frame,kept⟩:=extension_normal source current node payload data installed nodeCell payloadCell (by omega) normal
      let currentData:=data.of_frame frame
      have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [Input.LocalEffects.code_of_erase source current frame]; exact installed
      have currentDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
      change current.memaddrs=source.memaddrs at currentDomain
      have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
        (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame).trans heapCell
      have bound:=NodeRefLen.reference_bound data.child data.tag data.length
      change data.word.toNat≤33 at bound
      exact extension_buffer_cost current node heap compact length payload (payload+data.word) currentData (sized.of_frame frame) number
        currentInstalled (currentDomain.trans domain) ((kept _ (by decide)).trans nodeCell) ((kept _ (by decide)).trans tagCell)
        ((kept _ (by decide)).trans compactCell) ((kept _ (by decide)).trans lengthCell) payloadAfter currentHeap heapLower heapUpper aligned
        pathSmall small (by omega) pathBefore before)
  omega

/-- The whole unchanged extension body, including its actual four mapped
entry reads, real size call, allocation and path/reference writing. -/
theorem body_extension_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap compact length payload : BitVec 64)
    (entry : PreparedEntry source frame node 2#64 compact length payload)
    (data : ExtensionData source node) (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<heap.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice data.length.toNat+103 := by
  let current:=pathStart source 2#64 compact length payload
  let currentData:=data.of_frame (show Input.LocalEffects.erase current=Input.LocalEffects.erase source from rfl)
  have cells:=path_start_cells source 2#64 compact length payload
  have price:=extension_finish_cost current node heap compact length payload currentData (sized.of_frame rfl) installed domain
    (cells.2.2.2.2.trans entry.nodeCell) cells.1 cells.2.2.1 cells.2.2.2.1 cells.2.1 heapCell heapLower heapUpper aligned
    pathSmall small fits pathBefore before
  have same:=congrArg (fun observed=>observed.1.2) entry.observe
  change (evaluateHOLFiniteState source body).2.clock=(evaluateHOLFiniteState current afterLength).2.clock at same
  rw [same]
  exact price


/-- The reference inputs are actual registered fields, with HASH24 omitted. -/
theorem ExtensionData.Footprint.location {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ExtensionData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (query : BitVec 64) (required : data.Footprint query) : RegisteredField graph query := by
  have childMember:=data.child_member graph member active tag
  rcases required with equal|⟨live,equal⟩|⟨live,_nonHash,equal⟩|⟨live,_nonHash,_populated,equal⟩
  · refine ⟨node,48,member,active,?_,by decide,equal⟩
    rw [tag]
    decide
  · exact ⟨data.child,0,childMember,live,by have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child); omega,by decide,by simpa only [byteAddress,BitVec.add_zero] using equal⟩
  · exact ⟨data.child,8,childMember,live,by have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child); omega,by decide,equal⟩
  · exact ⟨data.child,16,childMember,live,by have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child); omega,by decide,equal⟩

theorem ExtensionData.footprint_before {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap : BitVec 64}
    (data : ExtensionData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (lower upper : Nat) (regions : graph.Regions lower upper) (before : upper≤heap.toNat)
    (query : BitVec 64) (required : data.Footprint query) : query.toNat<heap.toNat := by
  obtain ⟨owner,offset,ownerMember,ownerActive,inside,_notHash,equal⟩:=required.location data graph member active tag query
  rw [equal]
  exact Nat.lt_of_lt_of_le (graph.region_query_bounds lower upper regions owner offset ownerMember ownerActive inside).2 before

theorem ExtensionData.of_graph_length (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64) (lower upper : Nat) (regions : graph.Regions lower upper)
    (domain : source.memaddrs=InitE.ordinaryDomain) (limit : Nat) (bounded : CachedLengths graph limit) :
    (ExtensionData.of_graph source node graph member active tag lower upper regions domain).length.toNat≤limit := by
  let view:=graph.extension node member active tag
  change (if view.child=0#64 ∨ wordAt source.memory view.child=0#64 ∨ wordAt source.memory (view.child+8#64)=0#64
    then 0#64 else wordAt source.memory (view.child+16#64)).toNat≤limit
  split
  · change 0≤limit; omega
  · rename_i relevant
    have live : view.child≠0#64:=fun zero=>relevant (Or.inl zero)
    have nonHash : wordAt source.memory view.child≠0#64:=fun zero=>relevant (Or.inr (Or.inl zero))
    have populated : wordAt source.memory (view.child+8#64)≠0#64:=fun zero=>relevant (Or.inr (Or.inr zero))
    exact bounded view.child view.member live nonHash populated

/-- The whole extension body obtains its reference inputs and their earlier
locations from the actual graph; only real populated caches need a size cap. -/
theorem body_extension_graph_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node heap compact length payload : BitVec 64)
    (entry : PreparedEntry source frame node 2#64 compact length payload)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper : Nat) (regions : graph.Regions lower upper) (before : upper≤heap.toNat)
    (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit) (small : cacheLimit+136<2^64)
    (pathSmall : length.toNat+32<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice cacheLimit+103 := by
  have tag : wordAt source.memory node=2#64:=by simp [wordAt,entry.headerStored,MemoryBytes.wordBits]
  let data:=ExtensionData.of_graph source node graph member active tag lower upper regions domain
  have lengthBound:=ExtensionData.of_graph_length source node graph member active tag lower upper regions domain cacheLimit bounded
  have price:=body_extension_cost source frame node heap compact length payload entry data sized installed domain heapCell heapLower heapUpper aligned pathSmall
    (by change data.length.toNat+136<2^64; change data.length.toNat≤cacheLimit at lengthBound; omega) fits pathBefore
    (data.footprint_before graph member active tag lower upper regions before)
  have monotone : CurrentKeccak.Hash.bodyPrice data.length.toNat≤CurrentKeccak.Hash.bodyPrice cacheLimit:=by
    change data.length.toNat≤cacheLimit at lengthBound
    unfold CurrentKeccak.Hash.bodyPrice
    omega
  omega


/-- The physical separated queries retained by one genuine reference write. -/
structure ReferenceProtection (child buffer stp pad : BitVec 64) (keep : BitVec 64 → Prop) : Prop where
  earlier : ∀ query,keep query → query.toNat<buffer.toNat
  stateAway : ∀ query,keep query → CopyGeneral.Away stp query 200
  padAway : ∀ query,keep query → CopyGeneral.Away pad query 136
  cacheAway : child≠0#64 → ∀ query,keep query → query≠child+24#64
  cacheBefore : (child+24#64).toNat<2952790016
  stateBefore : stp.toNat+200≤2952790016
  padBefore : pad.toNat+136≤2952790016

/-- The same older persistent band is protected during the actual single
extension child write, including null references and fresh digest allocation. -/
theorem ReferenceProtection.with_band {child buffer stp pad : BitVec 64} {keep : BitVec 64 → Prop}
    (protection : ReferenceProtection child buffer stp pad keep) (lower : Nat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (cacheBefore : child≠0#64 → (child+24#64).toNat<lower) :
    ReferenceProtection child buffer stp pad (WithBand keep lower buffer.toNat) := by
  refine ⟨?_,?_,?_,?_,protection.cacheBefore,protection.stateBefore,protection.padBefore⟩
  · intro query required
    rcases required with original|band
    · exact protection.earlier query original
    · exact band.2
  · intro query required
    rcases required with original|band
    · exact protection.stateAway query original
    · exact CopyGeneral.Away.before stp query 200 lower stateBefore (by have small:=query.isLt; omega) band.1
  · intro query required
    rcases required with original|band
    · exact protection.padAway query original
    · exact CopyGeneral.Away.before pad query 136 lower padBefore (by have small:=query.isLt; omega) band.1
  · intro live query required
    rcases required with original|band
    · exact protection.cacheAway live query original
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      have before:=cacheBefore live
      omega

/-- A real reference normal result preserves each separated earlier word;
null references use their genuine destination-only frame. -/
theorem reference_write_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {child buffer offset heap cached stp pad : BitVec 64} {value : ValueHOL 64} {keep : BitVec 64 → Prop}
    (output : NodeWriteRef.Output source post child (buffer+offset) heap cached stp pad value)
    (noHash : child=0#64 → output.hashed=false) (protection : ReferenceProtection child buffer stp pad keep)
    (aligned : buffer.toNat%8=0) (heapFloor : buffer.toNat≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (inside : buffer.toNat+offset.toNat+output.bytes≤2952790016)
    (query : BitVec 64) (required : keep query) : post.memory query=source.memory query := by
  have before:=protection.earlier query required
  have dstNumber : (buffer+offset).toNat=buffer.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by omega)
  have dstAway:=CopyGeneral.Away.after_floor (buffer+offset) query output.bytes buffer.toNat aligned (by rw [dstNumber]; omega) (by rw [dstNumber]; omega) before
  by_cases null : child=0#64
  · exact output.fastMemory (noHash null) query dstAway
  · exact output.memory query dstAway (protection.cacheAway null query required) (protection.stateAway query required) (protection.padAway query required)
      (fun _hashed _zero=>CopyGeneral.Away.after_floor heap query 32 buffer.toNat aligned heapFloor (by omega) before)

theorem reference_write_metadata {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : NodeWriteRef.Output source post child dst heap cached stp pad value) :
    Rlp.Validation.scratchMetadata post=Rlp.Validation.scratchMetadata source := by
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) output.fields
  have base : Rlp.Validation.scratchMetadata (NodeWriteRef.outputBase source heap cached output.hashed)=Rlp.Validation.scratchMetadata source:=by
    unfold NodeWriteRef.outputBase
    split
    · unfold NodeHashCached.resultBase
      split <;> rfl
    · rfl
  exact projected.trans base

theorem hash_environment_of_metadata {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (environment : CurrentKeccak.Hash.Environment source stp pad) (frame : Input.MemoryMetadata.erase current=Input.MemoryMetadata.erase source) :
    CurrentKeccak.Hash.Environment current stp pad := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change current.globals=source.globals at globals
  exact ⟨by rw [Input.MemoryMetadata.code frame]; exact environment.installed,(Input.MemoryMetadata.domain frame).trans environment.domain,
    by rw [globals]; exact environment.stateGlobal,by rw [globals]; exact environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

/-- Compose genuine header allocation with an observed completed writer,
retaining its actual later heap and the earlier protected source words. -/
theorem BufferOutput.written_output {origin source written : PanSemStateFiniteExact 64 Guest.HostMemory}
    {buffer payload : BitVec 64} {header : Nat} {keep : BitVec 64 → Prop}
    (output : BufferOutput origin source buffer payload header) (completed : WrittenOutput source written buffer (header+payload.toNat) keep)
    (aligned : buffer.toNat%8=0) (earlier : ∀ query,keep query → query.toNat<buffer.toNat) :
    WrittenOutput origin written buffer (header+payload.toNat) keep := by
  have metadata : Rlp.Validation.scratchMetadata source=Rlp.Validation.scratchMetadata origin:=by
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) output.fields
    exact same
  have globals : HeapGlobals origin source:=by
    have same:=congrArg PanSemStateFiniteExact.globals output.fields
    change source.globals=(PersistentAlloc.post origin buffer (BitVec.ofNat 64 (header+payload.toNat))).globals at same
    intro key different
    rw [same]
    exact HeapGlobals.update origin _ key different
  exact ⟨completed.heap,⟨completed.runtime.1.trans output.runtime.1,completed.runtime.2.1.trans output.runtime.2.1,completed.runtime.2.2.trans output.runtime.2.2⟩,
    completed.metadata.trans metadata,globals.trans completed.globals,
    fun query required=>(completed.memory query required).trans (output.before aligned query (earlier query required)),
    fun query above=>(completed.scratch query above).trans (output.above_cap query above)⟩

/-- Both actual extension writes retain their true exact offset and the
whole physical result, including any genuine child hash and heap growth. -/
theorem extension_path_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node buffer offset compact length first heap stp pad : BitVec 64) (data : ExtensionData source node)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (keep : BitVec 64 → Prop) (protection : ReferenceProtection data.child buffer stp pad keep) (aligned : buffer.toNat%8=0)
    (before : ∀ query,data.Footprint query → query.toNat<buffer.toNat)
    (heapFloor : buffer.toNat+offset.toNat+Input.RlpLength.BytesSize.encodedLength first length+data.word.toNat≤heap.toNat)
    (digestMapped : data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64 → source.memaddrs (data.child+24#64))
    (firstRead : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first)))
    (normal : evaluateHOLFiniteState source pathWriteScope=(none,post)) :
    let bytes:=offset.toNat+Input.RlpLength.BytesSize.encodedLength first length+data.word.toNat
    post.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 bytes))) ∧ WrittenOutput source post buffer bytes keep ∧
      post.locals.lookup (ofString "node")=some (.val (.word node)) ∧ post.locals.lookup (ofString "buf")=some (.val (.word buffer)) := by
  let pathBytes:=Input.RlpLength.BytesSize.encodedLength first length
  let bytes:=offset.toNat+pathBytes+data.word.toNat
  let nextOffset:=offset+BitVec.ofNat 64 pathBytes
  obtain ⟨current,inner,endpoint,secondRun,currentOffset,firstFrame,kept⟩:=path_prefix_normal source post buffer offset compact length first environment.installed pathSmall
    bufferCell offsetCell compactCell lengthCell firstRead normal
  have firstFits : buffer.toNat+offset.toNat+pathBytes<2^64:=by omega
  let currentData:=data.of_memory (Input.MemoryMetadata.domain firstFrame.metadata)
    (fun query required=>path_frame_before firstFrame aligned firstFits query (before query required))
  have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):= (kept _ (by decide) (by decide)).trans nodeCell
  have currentBuffer : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):= (kept _ (by decide) (by decide)).trans bufferCell
  have currentTag : current.locals.lookup (ofString "k")=some (.val (.word 2#64)):= (kept _ (by decide) (by decide)).trans tagCell
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) firstFrame.metadata).trans heapCell
  have selected : evaluateHOLFiniteState current pathSecondChoice=evaluateHOLFiniteState current extensionWriteScope:=by
    rw [path_write_shapes.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected] at secondRun
  let cached:=wordAt current.memory (data.child+24#64)
  obtain ⟨output,size,noHash,finalOffset,finalNode,finalBuffer⟩:=extension_write_normal current inner node buffer nextOffset heap cached stp pad currentData
    (hash_environment_of_metadata environment firstFrame.metadata) heapLower currentNode currentBuffer currentOffset currentHeap heapUpper small
    (by intro live nonHash populated; exact ⟨by rw [Input.MemoryMetadata.domain firstFrame.metadata]; exact digestMapped live nonHash populated,reference_word_stored current.memory _⟩) secondRun
  let finalOutput:=output.reframe rfl (show Input.LocalEffects.erase post=Input.LocalEffects.erase inner from by rw [endpoint]; rfl)
  have nextNumber : nextOffset.toNat=offset.toNat+pathBytes:=by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inside : buffer.toNat+nextOffset.toNat+finalOutput.bytes≤2952790016:=by
    change buffer.toNat+nextOffset.toNat+output.bytes≤2952790016
    rw [size,nextNumber]
    change buffer.toNat+(offset.toNat+pathBytes)+data.word.toNat≤2952790016
    omega
  have dstNumber : (buffer+nextOffset).toNat=buffer.toNat+nextOffset.toNat:=BitVec.toNat_add_of_lt (by omega)
  have nextHeap:=finalOutput.heap currentHeap heapUpper heapAligned
  have currentMetadata : Rlp.Validation.scratchMetadata current=Rlp.Validation.scratchMetadata source:=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=HolFiniteMapExact.empty}) firstFrame.metadata
  have currentGlobals : HeapGlobals source current:=by
    intro key _different
    have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) firstFrame.metadata
    exact same
  have completed : WrittenOutput source post buffer bytes keep:=by
    refine ⟨⟨NodeWriteRef.outputHeap heap cached finalOutput.hashed,nextHeap.1,nextHeap.2.2.1,nextHeap.2.2.2,by dsimp only [bytes]; omega⟩,
      ⟨finalOutput.runtime.1.trans (Input.MemoryMetadata.domain firstFrame.metadata),finalOutput.runtime.2.1.trans (Input.MemoryMetadata.endian firstFrame.metadata),
        finalOutput.runtime.2.2.trans (Input.MemoryMetadata.code firstFrame.metadata)⟩,
      (reference_write_metadata finalOutput).trans currentMetadata,currentGlobals.trans finalOutput.heap_globals,?_,?_⟩
    · intro query required
      exact (reference_write_memory finalOutput noHash protection aligned (by omega) heapUpper inside query required).trans
        (path_frame_before firstFrame aligned firstFits query (protection.earlier query required))
    · intro query above
      have last:=finalOutput.above_cap (by rw [dstNumber]; exact inside) protection.cacheBefore protection.stateBefore protection.padBefore query above
      exact last.trans (firstFrame.memory query (CopyGeneral.Away.before (buffer+offset) query pathBytes 2952790016
        (by rw [BitVec.toNat_add_of_lt (by omega)]; omega) (by decide) above))
  have offsetEq : nextOffset+data.word=BitVec.ofNat 64 bytes:=by
    simp only [nextOffset,bytes,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
  refine ⟨?_,completed,?_,?_⟩
  · rw [endpoint,restore_lookup_other source inner "w" "off" (by decide),←offsetEq]
    exact finalOffset
  · rw [endpoint,restore_lookup_other source inner "w" "node" (by decide)]
    exact finalNode
  · rw [endpoint,restore_lookup_other source inner "w" "buf" (by decide)]
    exact finalBuffer


/-- The genuine allocation changes only heap_ptr among the hash globals. -/
theorem BufferOutput.hash_environment {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {buffer payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (environment : CurrentKeccak.Hash.Environment origin stp pad) :
    CurrentKeccak.Hash.Environment source stp pad := by
  have state:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup (ofString "keccak_st")) output.fields
  have padding:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup (ofString "keccak_pad")) output.fields
  have stateSame : source.globals.lookup (ofString "keccak_st")=origin.globals.lookup (ofString "keccak_st"):=by
    simpa [Input.MemoryMetadata.erase,PersistentAlloc.post,emptyLocalsHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using state
  have padSame : source.globals.lookup (ofString "keccak_pad")=origin.globals.lookup (ofString "keccak_pad"):=by
    simpa [Input.MemoryMetadata.erase,PersistentAlloc.post,emptyLocalsHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using padding
  exact ⟨by rw [output.runtime.2.2]; exact environment.installed,output.runtime.1.trans environment.domain,
    stateSame.trans environment.stateGlobal,padSame.trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

/-- The observed extension buffer prefix and actual compact/reference
writes compose with the literal cache footer into the whole physical result. -/
theorem BufferOutput.extension_writer_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node buffer compact length compactPayload payload stp pad : BitVec 64} {header : Nat}
    (output : BufferOutput origin source buffer payload header) (data : ExtensionData origin node)
    (sized : NodeRlpBegin.PathPayload origin node 2#64 compact length compactPayload)
    (exactPayload : payload.toNat=compactPayload.toNat+data.word.toNat)
    (environment : CurrentKeccak.Hash.Environment origin stp pad)
    (nodeCell : origin.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : origin.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (compactCell : origin.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : origin.locals.lookup (ofString "clen")=some (.val (.word length)))
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64)
    (pathBefore : compact.toNat+length.toNat≤buffer.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<buffer.toNat)
    (keep : BitVec 64 → Prop) (protection : ReferenceProtection data.child buffer stp pad keep) (aligned : buffer.toNat%8=0)
    (digestMapped : data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64 → origin.memaddrs (data.child+24#64))
    (pointerMapped : origin.memaddrs (node+8#64)) (lengthMapped : origin.memaddrs (node+16#64)) (nodeBefore : node.toNat+24≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source writerTail=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ FinishOutput origin post node buffer (header+payload.toNat) keep := by
  obtain ⟨first,_valueFirst,firstRead,_valueRead,exactCompact⟩:=sized
  have compactExact : compactPayload.toNat=Input.RlpLength.BytesSize.encodedLength first length:=by simpa using exactCompact
  let currentData:=data.of_memory output.runtime.1 (fun query required=>output.before aligned query (before query required))
  have currentFirst : length=1#64 → eval source (.loadByte (.const compact))=some (.val (.word first)):=by
    intro one
    have number : length.toNat=1:=by rw [one]; rfl
    exact NodeRlpBegin.sizing_byte_agreement origin source compact first output.runtime.1 output.runtime.2.1
      (output.before aligned _ (by rw [AllocatedBytes.aligned_number]; omega)) (firstRead one)
  have currentNode : source.locals.lookup (ofString "node")=some (.val (.word node)):=
    (output.locals _ (by decide) (by decide) (by decide)).trans nodeCell
  have currentTag : source.locals.lookup (ofString "k")=some (.val (.word 2#64)):=
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
  have spanExact : (BitVec.ofNat 64 header).toNat+Input.RlpLength.BytesSize.encodedLength first length+currentData.word.toNat=header+payload.toNat:=by
    change (BitVec.ofNat 64 header).toNat+Input.RlpLength.BytesSize.encodedLength first length+data.word.toNat=header+payload.toNat
    rw [offsetNumber]
    omega
  obtain ⟨offset,completed,writtenNode,writtenBuffer⟩:=extension_path_normal source written node buffer (BitVec.ofNat 64 header) compact length first
    (PersistentAlloc.rounded buffer (BitVec.ofNat 64 (header+payload.toNat))) stp pad currentData (output.hash_environment environment) output.heapCell
    (by have floor:=output.growth; have lower:=output.arena.lower; omega) output.heapUpper output.heapAligned pathSmall small
    currentNode currentTag output.bufferCell output.offsetCell currentCompact currentLength keep protection aligned before
    (by have floor:=output.growth; omega)
    (by intro live nonHash populated; rw [output.runtime.1]; exact digestMapped live nonHash populated) currentFirst pathRun
  rw [spanExact] at offset completed
  have result:=output.written_output completed aligned protection.earlier
  exact result.footer writtenNode writtenBuffer offset pointerMapped lengthMapped nodeBefore value footerRun


/-- Complete actual extension normal result, from its original compact
payload through real reference-size preparation, allocation and writing. -/
theorem extension_finish_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node heap compact length payload stp pad : BitVec 64) (data : ExtensionData source node)
    (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 2#64)))
    (compactCell : source.locals.lookup (ofString "cbuf")=some (.val (.word compact)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<heap.toNat)
    (keep : BitVec 64 → Prop) (protection : ReferenceProtection data.child heap stp pad keep)
    (digestMapped : data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64 → source.memaddrs (data.child+24#64))
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64)) (nodeBefore : node.toNat+24≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLength=(some (.returned value),post)) :
    ∃ header,value=.val (.word 0#64) ∧ header=Input.RlpLength.Header.encodedLength (payload+data.word) ∧
      FinishOutput source post node heap (header+(payload+data.word).toNat) keep := by
  have selected : evaluateHOLFiniteState source extensionChoice=evaluateHOLFiniteState source extensionScope:=by
    rw [entry_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have safe : Input.LocalPrefix (ofString "node") extensionChoice:=by
    rw [entry_shapes.2.2]
    apply Input.LocalPrefix.ite
    · rw [extension_shape]
      exact .decCall _ _ _ _ (by decide) (.assign _ _ (by decide))
    · exact .skip
  rw [entry_shapes.2.1] at normal
  obtain ⟨prepared,prepareRun,allocationRun⟩:=Input.sequence_returned source post extensionChoice afterExtension value (safe.summary_full source).2.1 normal
  rw [selected] at prepareRun
  obtain ⟨payloadAfter,number,_populated,frame,kept⟩:=extension_normal source prepared node payload data environment.installed nodeCell payloadCell (by omega) prepareRun
  let preparedData:=data.of_frame frame
  have preparedEnvironment:=environment.of_frame frame
  have preparedHeap : prepared.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
    (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame).trans heapCell
  have preparedTag : prepared.locals.lookup (ofString "k")=some (.val (.word 2#64)):= (kept _ (by decide)).trans tagCell
  rw [path_after_extension prepared 2#64 preparedTag (by decide)] at allocationRun
  have bound:=NodeRefLen.reference_bound data.child data.tag data.length
  change data.word.toNat≤33 at bound
  obtain ⟨current,inner,header,_trace,output,scope,continued⟩:=buffer_return prepared post heap (payload+data.word) preparedEnvironment.installed payloadAfter preparedHeap
    heapLower heapUpper (by omega) value allocationRun
  have result:=output.extension_writer_normal preparedData (sized.of_frame frame) number preparedEnvironment
    ((kept _ (by decide)).trans nodeCell) preparedTag ((kept _ (by decide)).trans compactCell) ((kept _ (by decide)).trans lengthCell)
    pathSmall small pathBefore before keep protection aligned
    (by intro live nonHash populated; rw [preparedEnvironment.domain,←environment.domain]; exact digestMapped live nonHash populated)
    (by rw [preparedEnvironment.domain,←environment.domain]; exact pointerMapped)
    (by rw [preparedEnvironment.domain,←environment.domain]; exact lengthMapped) nodeBefore value continued
  exact ⟨header,result.1,output.headerExact,result.2.reframe frame.symm scope.metadata⟩

/-- The whole unchanged extension body returns its exact cache and physical
serializer frame through all real entry reads and lexical restoration. -/
theorem body_extension_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame node heap compact length payload stp pad : BitVec 64) (entry : PreparedEntry source frame node 2#64 compact length payload)
    (data : ExtensionData source node) (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (pathSmall : length.toNat+32<2^64) (small : data.length.toNat+136<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (before : ∀ query,data.Footprint query → query.toNat<heap.toNat)
    (keep : BitVec 64 → Prop) (protection : ReferenceProtection data.child heap stp pad keep)
    (digestMapped : data.child≠0#64 → data.tag≠0#64 → data.cached≠0#64 → source.memaddrs (data.child+24#64))
    (pointerMapped : source.memaddrs (node+8#64)) (lengthMapped : source.memaddrs (node+16#64)) (nodeBefore : node.toNat+24≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header,value=.val (.word 0#64) ∧ header=Input.RlpLength.Header.encodedLength (payload+data.word) ∧
      FinishOutput source post node heap (header+(payload+data.word).toNat) keep := by
  let current:=pathStart source 2#64 compact length payload
  let inner:=(evaluateHOLFiniteState current afterLength).2
  let currentData:=data.of_frame (show Input.LocalEffects.erase current=Input.LocalEffects.erase source from rfl)
  have cells:=path_start_cells source 2#64 compact length payload
  have observed:=entry.observe
  rw [normal] at observed
  have outcome:=congrArg (fun observation=>observation.1.1) observed
  change some (.returned value)=(evaluateHOLFiniteState current afterLength).1 at outcome
  have run : evaluateHOLFiniteState current afterLength=(some (.returned value),inner):=Prod.ext outcome.symm rfl
  have scope:=congrArg Prod.snd observed
  change Input.LocalEffects.erase post=Input.LocalEffects.erase inner at scope
  obtain ⟨header,answer,exactHeader,output⟩:=extension_finish_normal current inner node heap compact length payload stp pad currentData (sized.of_frame rfl) (environment.of_frame rfl)
    (cells.2.2.2.2.trans entry.nodeCell) cells.1 cells.2.2.1 cells.2.2.2.1 cells.2.1 heapCell heapLower heapUpper aligned
    pathSmall small fits pathBefore before keep protection digestMapped pointerMapped lengthMapped nodeBefore value run
  exact ⟨header,answer,exactHeader,output.reframe rfl scope⟩


/-- Registered node fields, full stored paths and earlier input words are
separate from this child's real hash writes by their actual allocation layout. -/
theorem ReferenceProtection.of_graph {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer stp pad : BitVec 64}
    (data : ExtensionData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (beforeBuffer : upper≤buffer.toNat) (belowCap : upper≤2952790016)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824) :
    ReferenceProtection data.child buffer stp pad (SerializerQueries graph inputEnd) := by
  have parent:=regions node member active
  have nodeSize:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
  have childMember:=data.child_member graph member active tag
  have queryBounds : ∀ query,RegisteredField graph query → lower≤query.toNat ∧ query.toNat<upper:=by
    intro query ⟨owner,offset,ownerMember,live,inside,_notHash,equal⟩
    rw [equal]
    exact graph.region_query_bounds lower upper regions owner offset ownerMember live inside
  have pathBounds : ∀ query,PathQuery graph query → lower≤query.toNat ∧ query.toNat<upper:=by
    intro query ⟨owner,ownerMember,ownerActive,ownerTag,index,inside,equal⟩
    have span:=paths.span owner ownerMember ownerActive ownerTag
    have bounds:=pathRegions owner ownerMember ownerActive ownerTag
    have number:=byteAddress_toNat (wordAt source.memory (owner+32#64)) index (by have fits:=span.fits; omega)
    rw [equal,AllocatedBytes.aligned_number,number]
    omega
  refine ⟨?_,?_,?_,?_,?_,by omega,by omega⟩
  · intro query required
    rcases required with field|path
    · rcases field with field|input
      · have bounds:=queryBounds query field; omega
      · omega
    · have bounds:=pathBounds query path; omega
  · intro query required
    rcases required with field|path
    · rcases field with field|input
      · have bounds:=queryBounds query field
        exact CopyGeneral.Away.before stp query 200 lower stateBefore (by have small:=query.isLt; omega) bounds.1
      · exact CopyGeneral.Away.before stp query 200 2701134824 stateBeforeInput (by decide) input.1
    · have bounds:=pathBounds query path
      exact CopyGeneral.Away.before stp query 200 lower stateBefore (by have small:=query.isLt; omega) bounds.1
  · intro query required
    rcases required with field|path
    · rcases field with field|input
      · have bounds:=queryBounds query field
        exact CopyGeneral.Away.before pad query 136 lower padBefore (by have small:=query.isLt; omega) bounds.1
      · exact CopyGeneral.Away.before pad query 136 2701134824 padBeforeInput (by decide) input.1
    · have bounds:=pathBounds query path
      exact CopyGeneral.Away.before pad query 136 lower padBefore (by have small:=query.isLt; omega) bounds.1
  · intro live query required
    rcases required with field|⟨owner,ownerMember,ownerActive,ownerTag,index,within,equal⟩
    · rcases field with ⟨owner,offset,ownerMember,ownerLive,within,notHash,equal⟩|input
      · rw [equal]
        exact graph.cache_away lower upper regions disjoint data.child owner offset childMember live ownerMember ownerLive within notHash
      · have childRegion:=regions data.child childMember live
        have number : (data.child+24#64).toNat=data.child.toNat+24:=byteAddress_toNat data.child 24
          (by have cap:=childRegion.2.1.upper; have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child); omega)
        intro equal
        have numeric:=congrArg BitVec.toNat equal
        rw [number] at numeric
        omega
    · rw [equal]
      have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child)
      exact separated owner ownerMember ownerActive ownerTag index within data.child childMember live 24 (by omega)
  · by_cases null : data.child=0#64
    · rw [null]; decide
    · have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child)
      have bounds:=graph.region_query_bounds lower upper regions data.child 24 childMember null (by omega)
      change lower≤(data.child+24#64).toNat ∧ (data.child+24#64).toNat<upper at bounds
      omega


/-- The complete actual extension normal body obtains every protected
query/cache mapping from the incoming graph, paths and physical workspace.
Its observed heap also bounds the newly stored serialized byte count. -/
theorem body_extension_graph_normal_band (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame node heap compact length payload stp pad : BitVec 64) (entry : PreparedEntry source frame node 2#64 compact length payload)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) (before : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit) (small : cacheLimit+136<2^64)
    (pathSmall : length.toNat+32<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤2952790016 ∧ FinishOutput source post node heap bytes (WithBand (SerializerQueries graph inputEnd) upper heap.toNat) := by
  have tag : wordAt source.memory node=2#64:=by simp [wordAt,entry.headerStored,MemoryBytes.wordBits]
  let data:=ExtensionData.of_graph source node graph member active tag lower upper regions environment.domain
  have lengthBound:=ExtensionData.of_graph_length source node graph member active tag lower upper regions environment.domain cacheLimit bounded
  have originalProtection:=ReferenceProtection.of_graph data graph member active tag lower upper inputEnd regions disjoint paths pathRegions separated lowerAligned environment before
    (before.trans heapUpper) stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput
  have ordered : lower≤upper:=by have parent:=regions node member active; omega
  have protection:=originalProtection.with_band upper (stateBefore.trans ordered) (padBefore.trans ordered) (by
    intro live
    have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory data.child)
    exact (graph.region_query_bounds lower upper regions data.child 24 (data.child_member graph member active tag) live (by omega)).2)
  have parent:=regions node member active
  have nodeBefore : node.toNat+24≤2952790016:=by
    have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
    omega
  obtain ⟨header,answer,_exactHeader,output⟩:=body_extension_normal source post frame node heap compact length payload stp pad entry data sized environment heapCell heapLower heapUpper aligned
    pathSmall (by change data.length.toNat≤cacheLimit at lengthBound; omega) fits pathBefore (data.footprint_before graph member active tag lower upper regions before)
    (WithBand (SerializerQueries graph inputEnd) upper heap.toNat) protection
    (by intro live _nonHash _populated; exact reference_cache_mapped source graph lower upper regions environment.domain data.child (data.child_member graph member active tag) live 24 (by decide) (by decide))
    (reference_cache_mapped source graph lower upper regions environment.domain node member active 8 (by decide) (by decide))
    (reference_cache_mapped source graph lower upper regions environment.domain node member active 16 (by decide) (by decide)) nodeBefore value normal
  obtain ⟨next,_cell,cap,_aligned,floor⟩:=output.heap
  exact ⟨header+(payload+data.word).toNat,answer,by omega,output⟩


/-- Existing original-query interface follows from the stronger real band result. -/
theorem body_extension_graph_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame node heap compact length payload stp pad : BitVec 64) (entry : PreparedEntry source frame node 2#64 compact length payload)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (lower upper inputEnd : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions lower upper) (separated : graph.PathSeparated) (lowerAligned : lower%8=0)
    (sized : NodeRlpBegin.PathPayload source node 2#64 compact length payload) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) (before : upper≤heap.toNat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (inputBeforeNodes : inputEnd≤lower)
    (stateBeforeInput : stp.toNat+200≤2701134824) (padBeforeInput : pad.toNat+136≤2701134824)
    (cacheLimit : Nat) (bounded : CachedLengths graph cacheLimit) (small : cacheLimit+136<2^64)
    (pathSmall : length.toNat+32<2^64) (fits : payload.toNat+42<2^64)
    (pathBefore : compact.toNat+length.toNat≤heap.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤2952790016 ∧ FinishOutput source post node heap bytes (SerializerQueries graph inputEnd) := by
  obtain ⟨bytes,answer,bound,output⟩:=body_extension_graph_normal_band source post frame node heap compact length payload stp pad entry graph member active
    lower upper inputEnd regions disjoint paths pathRegions separated lowerAligned sized environment heapCell heapLower heapUpper aligned before
    stateBefore padBefore inputBeforeNodes stateBeforeInput padBeforeInput cacheLimit bounded small pathSmall fits pathBefore value normal
  exact ⟨bytes,answer,bound,output.weaken_keep (fun _ required=>Or.inl required)⟩

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

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.of_frame

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.child_member

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.of_graph

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.size_arguments

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.of_memory

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.writer_bytes

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.hash_data

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.writer_arguments

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_write_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_write_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_write_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_after_compact_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_path_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.extension_writer_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.path_after_extension

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_buffer_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_finish_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_extension_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.Footprint.location

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.footprint_before

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ExtensionData.of_graph_length

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_extension_graph_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.reference_write_memory

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.reference_write_metadata

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.hash_environment_of_metadata

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.written_output

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_path_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.hash_environment

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.BufferOutput.extension_writer_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.extension_finish_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_extension_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceProtection.of_graph

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_extension_graph_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceProtection.with_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.body_extension_graph_normal_band

import InitECandidate.Solver.Mpt.NodeRlpFinishBranchNormal

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

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

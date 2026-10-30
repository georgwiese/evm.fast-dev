import InitECandidate.Solver.Input.CurrentRlp.WideWrite
import InitECandidate.Solver.Input.HeaderEncoding.FieldBounds
import InitECandidate.Solver.Input.AssignedCallKnown

namespace InitECandidate.Solver.Input.CurrentRlp.FieldWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open HeaderEncoding

/-- The real field arguments and current callee, its unconditional price,
and the physical facts derived only from that same callee's normal return. -/
def Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (field : Field) : Prop :=
  ∃ values program callee,
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (arguments field)=some values ∧
    lookupCodeHOLFinite source.code.lookup (ofString (functionName field)) values=some (program,callee,.one) ∧
    (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) program).2.clock≤maxCost field-1 ∧
    ∀ target value,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) program=(some (.returned value),target)→
      ∃ encoded,1≤encoded ∧ encoded≤maxSize field ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
        MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer

theorem arguments_two (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (left right : ValueHOL 64)
    (readFirst : eval source first=some left) (readSecond : eval source second=some right) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second]=some [left,right] := by
  simp only [eval] at readFirst readSecond
  simp only [evalListHOLFinite,evalListHOLExact,readFirst,readSecond]

theorem arguments_three (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second third : ExpHOL 64) (left middle right : ValueHOL 64)
    (readFirst : eval source first=some left) (readSecond : eval source second=some middle) (readThird : eval source third=some right) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,third]=some [left,middle,right] := by
  simp only [eval] at readFirst readSecond readThird
  simp only [evalListHOLFinite,evalListHOLExact,readFirst,readSecond,readThird]

theorem prepare_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer pointer : BitVec 64)
    (field : Field) (position length : Nat) (context : Context source original header buffer)
    (installed : OriginalCode.Installed source.code) (inside : position+maxSize field≤1024) (small : length≤256)
    (sizeBound : length+9≤maxSize field) (costBound : length+21≤maxCost field)
    (arena : AllocatedBytes.Arena pointer length)
    (function : functionName field="rlp_encode_bytes")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (arguments field)=
      some [.val (.word (address buffer position)),.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]) :
    Prepared source original header buffer field := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup (address buffer position) pointer (BitVec.ofNat 64 length)
    (BytesWrite.original_code source.code installed)
  have destination:=context.geometry.position_arena header buffer position (length+9) (by omega)
  have positionNumber:=context.geometry.position_number header buffer position (by omega)
  refine ⟨_,BytesWrite.body,callee,args,?_,?_,?_⟩
  · simpa only [function,BytesWrite.current_body] using called
  · have price:=BytesWrite.body_cost (callEntryStateHOLFinite source callee) (address buffer position) pointer length (by omega)
      installed context.domain d s n arena destination
    omega
  · intro target value normal
    obtain ⟨encoded,lower,positive,upper,number,answer,price,frame⟩:=BytesWrite.body_normal (callEntryStateHOLFinite source callee) target
      (address buffer position) pointer length (by omega) installed context.domain d s n arena destination value normal
    refine ⟨encoded,positive,by omega,answer,frame.metadata,?_⟩
    intro query before
    have away:=before_away (address buffer position) query (length+9) buffer.toNat destination (by omega) context.geometry.bufferAligned before
    exact (frame.memory query away).trans (context.oldMemory query before)

/-- Prepare every actual header field using only earlier buffer ownership.
The temporary wide-writer room is obtained from its own normal execution. -/
theorem prepare (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (field : Field) (position : Nat) (context : Context source original header buffer)
    (installed : OriginalCode.Installed source.code) (bounded : (cursor buffer).toNat≤2952790016)
    (facts : FieldFacts original header field) (inside : position+maxSize field≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position)))) :
    Prepared source original header buffer field := by
  have pRead : eval source (localVar "p")=some (.val (.word (address buffer position))) := by
    simp [eval,localVar,evalHOLExact,toExact,p]
  have positionNumber:=context.geometry.position_number header buffer position (by cases field <;> simp only [maxSize] at inside <;> omega)
  cases field with
  | bytes offset length=>
    obtain ⟨offsetBound,aligned,lengthBound,arena⟩:=facts
    have pointerRead:=context.load_one source original header buffer offset offsetBound aligned
    have args:=arguments_three source (localVar "p") (loadOne offset) (.const (BitVec.ofNat 64 length)) _ _ _ pRead pointerRead rfl
    exact prepare_bytes source original header buffer (wordAt original (address header offset)) (.bytes offset length) position length context installed inside
      lengthBound (by simp [maxSize]) (by simp [maxCost]) arena rfl args
  | extra=>
    obtain ⟨lengthBound,arena⟩:=facts
    let length:=(wordAt original (address header 136)).toNat
    have pointerRead:=context.load_one source original header buffer 128 (by decide) (by decide)
    have rawRead:=context.load_one source original header buffer 136 (by decide) (by decide)
    have lengthRead : eval source (loadOne 136)=some (.val (.word (BitVec.ofNat 64 length))) := by simpa [length] using rawRead
    have args:=arguments_three source (localVar "p") (loadOne 128) (loadOne 136) _ _ _ pRead pointerRead lengthRead
    exact prepare_bytes source original header buffer (wordAt original (address header 128)) .extra position length context installed inside
      (by dsimp [length]; omega) (by change length+9≤41; dsimp [length]; omega)
      (by change length+21≤53; dsimp [length]; omega) arena rfl args
  | scalar offset=>
    obtain ⟨offsetBound,aligned⟩:=facts
    have valueRead:=context.load_one source original header buffer offset offsetBound aligned
    have args:=arguments_two source (localVar "p") (loadOne offset) _ _ pRead valueRead
    obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup (address buffer position) (wordAt original (address header offset))
      (WordWrite.original_code source.code installed)
    have destination:=context.geometry.position_arena header buffer position 9 inside
    refine ⟨_,WordWrite.body,callee,args,called,?_,?_⟩
    · exact WordWrite.body_cost (callEntryStateHOLFinite source callee) _ _ installed d w
    · intro target value normal
      obtain ⟨encoded,positive,upper,answer,price,frame⟩:=WordWrite.body_normal (callEntryStateHOLFinite source callee) target _ _ installed d w value normal
      refine ⟨encoded,positive,upper,answer,frame.metadata,?_⟩
      intro query before
      have away:=before_away (address buffer position) query 9 buffer.toNat destination (by omega) context.geometry.bufferAligned before
      exact (frame.memory query away).trans (context.oldMemory query before)
  | wide offset=>
    obtain ⟨offsetBound,aligned⟩:=facts
    have valueRead:=context.load_wide source original header buffer offset offsetBound aligned
    have args:=arguments_two source (localVar "p") (loadWide offset) _ _ pRead valueRead
    obtain ⟨callee,called,d,v⟩:=RlpWrite.U256Put.environment source.code.lookup (address buffer position) (wideWords original header offset)
      (WideWrite.original_code source.code installed)
    have destination:=context.geometry.position_arena header buffer position 41 inside
    have cursorNumber:=context.geometry.cursor_number header buffer
    have bufferArena:=context.geometry.buffer_arena header buffer
    have temporary : AllocatedBytes.Arena (cursor buffer) 32:=AllocatedBytes.Arena.subrange buffer 1056 1024 32 bufferArena (by decide)
    have cursorLower : 2701131776≤(cursor buffer).toNat:=by rw [cursorNumber]; have lower:=bufferArena.lower; omega
    refine ⟨_,WideWrite.body,callee,args,called,?_,?_⟩
    · exact WideWrite.body_cost (callEntryStateHOLFinite source callee) _ _ _ installed context.domain v d context.heap cursorLower bounded destination
    · intro target value normal
      obtain ⟨encoded,positive,upper,number,answer,price,frame⟩:=WideWrite.body_normal (callEntryStateHOLFinite source callee) target _ _ _
        installed context.domain v d context.heap cursorLower bounded destination value normal
      refine ⟨encoded,positive,upper,answer,frame.metadata,?_⟩
      intro query before
      have away:=before_away (address buffer position) query 41 buffer.toNat destination (by omega) context.geometry.bufferAligned before
      have tmpAway:=before_away (cursor buffer) query 32 buffer.toNat temporary (by omega) context.geometry.bufferAligned before
      exact (frame.memory query away tmpAway).trans (context.oldMemory query before)

/-- Price an actual assigned field call on every outcome. -/
theorem Prepared.call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (field : Field) (ready : Prepared source original header buffer field) :
    source.clock-(evaluateHOLFiniteState source (call field)).2.clock≤maxCost field := by
  obtain ⟨values,program,callee,args,called,price,normal⟩:=ready
  have priced:=ClockCost.call_current source (some (some (ofString "w"))) (ofString (functionName field)) (arguments field)
    values program callee .one (maxCost field-1) args called price
  have positive : 1≤maxCost field:=by cases field <;> simp [maxCost]
  change source.clock-(evaluateHOLFiniteState source (call field)).2.clock≤maxCost field-1+1 at priced
  omega

/-- A genuine continuing field call restores the caller locals and retains
its earlier header image and heap. Only the actual result binding changes. -/
theorem Prepared.call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (field : Field) (context : Context source original header buffer)
    (ready : Prepared source original header buffer field)
    (normal : evaluateHOLFiniteState source (call field)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤maxSize field ∧ Context post original header buffer ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      post.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ name : String,ofString "w"≠ofString name→post.locals.lookup (ofString name)=source.locals.lookup (ofString name)) := by
  obtain ⟨values,program,callee,args,called,price,back⟩:=ready
  obtain ⟨funded,target,value,bodyRun,endpoint⟩:=CallNormal.local_known source post (ofString "w") (ofString (functionName field))
    (arguments field) values program callee .one args called normal
  obtain ⟨encoded,positive,upper,answer,metadata,memory⟩:=back target value bodyRun
  subst value
  rw [endpoint]
  have others (name : String) (different : ofString "w"≠ofString name) :
      (setVarHOLFinite (ofString "w") (.val (.word (BitVec.ofNat 64 encoded))) {target with locals:=source.locals}).locals.lookup (ofString name)=
        source.locals.lookup (ofString name):=bind_lookup_other {target with locals:=source.locals} "w" name _ different
  have globalFrame:=congrArg PanSemStateFiniteExact.globals metadata
  refine ⟨encoded,positive,upper,⟨context.geometry,(MemoryMetadata.domain metadata).trans context.domain,memory,
    (others "h" (by decide)).trans context.headerLocal,?_⟩,metadata,bind_lookup_same _ _ _,others⟩
  change target.globals=source.globals at globalFrame
  change target.globals.lookup (ofString "heap_ptr")=_
  rw [globalFrame]
  exact context.heap

/-- Normal call-and-advance derives the next natural output position;
all other caller locals and earlier physical header cells are retained. -/
theorem Prepared.step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (field : Field) (position : Nat) (context : Context source original header buffer)
    (ready : Prepared source original header buffer field)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (normal : evaluateHOLFiniteState source (.seq (call field) advance)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤maxSize field ∧ Context post original header buffer ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      post.locals.lookup (ofString "p")=some (.val (.word (address buffer (position+encoded)))) ∧
      post.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      (∀ name : String,ofString "p"≠ofString name→ ofString "w"≠ofString name→
        post.locals.lookup (ofString name)=source.locals.lookup (ofString name)) := by
  obtain ⟨middle,called,advanced⟩:=sequence_none source post _ _ normal
  obtain ⟨encoded,positive,upper,nextContext,metadata,w,others⟩:=ready.call_normal source middle original header buffer field context called
  have middleP:=(others "p" (by decide)).trans p
  have read : eval middle advanceExpression=some (.val (.word (address buffer (position+encoded)))):=by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,middleP,w,valueIsWord,valueWord,wordOpHOL,wordOp,
      address,BitVec.ofNat_add,BitVec.add_assoc]
  have endpoint:=assign_none middle post "p" advanceExpression (address buffer (position+encoded)) read advanced
  rw [endpoint]
  have otherP (name : String) (different : ofString "p"≠ofString name) :
      (bind middle "p" (address buffer (position+encoded))).locals.lookup (ofString name)=middle.locals.lookup (ofString name):=
    bind_lookup_other _ "p" name _ different
  exact ⟨encoded,positive,upper,⟨nextContext.geometry,nextContext.domain,nextContext.oldMemory,
    (otherP "h" (by decide)).trans nextContext.headerLocal,nextContext.heap⟩,metadata,bind_lookup_same _ _ _,
    (otherP "w" (by decide)).trans w,fun name pNe wNe=>(otherP name pNe).trans (others name wNe)⟩

end InitECandidate.Solver.Input.CurrentRlp.FieldWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.prepare_bytes
#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.prepare

#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.Prepared.call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.Prepared.call_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.Prepared.step_normal

namespace InitECandidate.Solver.Input.CurrentRlp.FieldWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

/-- Uniform field allowances when no decoded parent-record image survives.
Only the one variable extra-data field uses the finite-domain fallback. -/
def currentSize : Field→Nat
  | .bytes _ length=>length+9
  | .extra=>CopyAny.ordinaryEnd+40
  | .scalar _=>9
  | .wide _=>41

def currentPrice : Field→Nat
  | .bytes _ length=>CopyAny.price length+21
  | .extra=>43314052496
  | .scalar _=>19
  | .wide _=>134

def SmallField : Field→Prop
  | .bytes _ length=>length+32<2^64
  | _=>True

/-- Every outcome of the unchanged dynamic field call. Reads need not be
successful and the parent record needs no ownership/image premise. -/
theorem current_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) (small : SmallField field) :
    source.clock-(evaluateHOLFiniteState source (call field)).2.clock≤currentPrice field := by
  cases field with
  | bytes offset length=>
    exact BytesWrite.dynamic_known_length_cost source (some (some (ofString "w"))) (localVar "p") (loadOne offset) length small installed domain
  | extra=>
    exact BytesWrite.dynamic_domain_cost source (some (some (ofString "w"))) (localVar "p") (loadOne 128) (loadOne 136) installed domain
  | scalar offset=>
    exact WordWrite.dynamic_cost source (some (some (ofString "w"))) (localVar "p") (loadOne offset) installed
  | wide offset=>
    exact WideWrite.dynamic_current_cost source (some (some (ofString "w"))) (localVar "p") (loadWide offset) heap installed domain heapCell lower bounded

/-- A real normal field call derives its returned encoded size, full heap/
metadata and earlier-memory frame from the actual read arguments. -/
theorem current_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (field : Field) (pointer heap : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) (small : SmallField field)
    (headerFits : pointer.toNat+9<2^64) (positiveFloor : 0<floor) (aligned : floor%8=0)
    (afterFloor : floor≤pointer.toNat) (beforeHeap : floor≤heap.toNat)
    (normal : evaluateHOLFiniteState source (call field)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤currentSize field ∧
      post.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<floor→post.memory query=source.memory query) ∧
      ∀ key : MlS,key≠ofString "w"→post.locals.lookup key=source.locals.lookup key := by
  obtain ⟨funded,values,actual,callee,shape,child,returned,args,called,run,checked,endpoint⟩:=
    CallNormal.local_data source post (ofString "w") (ofString (functionName field)) (arguments field) normal
  have pointerRead : eval source (localVar "p")=some (.val (.word pointer)):=by
    simp [eval,evalHOLExact,toExact,localVar,p]
  cases field with
  | bytes offset length=>
    obtain ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩:=BytesWrite.current_argument_entry source
      (localVar "p") (loadOne offset) (.const (BitVec.ofNat 64 length)) values actual callee shape installed args called
    have dstEq : dst=pointer:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using (firstRead.symm.trans pointerRead)
    have countEq : count=BitVec.ofNat 64 length:=by
      simpa only [eval,evalHOLExact,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using thirdRead.symm
    subst dst
    subst count
    have knownArgs:=args.trans (congrArg some valuesEq)
    obtain ⟨encoded,positive,upper,uniform,w,metadata,memory,others⟩:=BytesWrite.assigned_current_normal source post (ofString "w")
      (arguments (.bytes offset length)) pointer src (BitVec.ofNat 64 length) floor installed domain knownArgs headerFits positiveFloor aligned afterFloor normal
    have number : (BitVec.ofNat 64 length).toNat=length:=by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by change length+32<2^64 at small; omega)]
    rw [number] at upper
    exact ⟨encoded,positive,upper,w,metadata,memory,others⟩
  | extra=>
    obtain ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩:=BytesWrite.current_argument_entry source
      (localVar "p") (loadOne 128) (loadOne 136) values actual callee shape installed args called
    have dstEq : dst=pointer:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using (firstRead.symm.trans pointerRead)
    subst dst
    have knownArgs:=args.trans (congrArg some valuesEq)
    obtain ⟨encoded,positive,upper,uniform,w,metadata,memory,others⟩:=BytesWrite.assigned_current_normal source post (ofString "w")
      (arguments .extra) pointer src count floor installed domain knownArgs headerFits positiveFloor aligned afterFloor normal
    exact ⟨encoded,positive,uniform,w,metadata,memory,others⟩
  | scalar offset=>
    obtain ⟨dst,word,valuesEq,firstRead,secondRead,bodyEq,d,w⟩:=WordWrite.current_argument_entry source
      (localVar "p") (loadOne offset) values actual callee shape installed args called
    have dstEq : dst=pointer:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using (firstRead.symm.trans pointerRead)
    subst dst
    have knownArgs:=args.trans (congrArg some valuesEq)
    exact WordWrite.assigned_current_normal source post (ofString "w") (arguments (.scalar offset)) pointer word floor installed knownArgs
      headerFits aligned afterFloor normal
  | wide offset=>
    obtain ⟨dst,words,valuesEq,firstRead,secondRead,bodyEq,d,v⟩:=WideWrite.current_argument_entry source
      (localVar "p") (loadWide offset) values actual callee shape installed args called
    have dstEq : dst=pointer:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using (firstRead.symm.trans pointerRead)
    subst dst
    have knownArgs:=args.trans (congrArg some valuesEq)
    exact WideWrite.assigned_current_normal source post (ofString "w") (arguments (.wide offset)) pointer heap words floor installed domain knownArgs
      heapCell lower bounded headerFits positiveFloor aligned afterFloor beforeHeap normal

/-- The real pointer advance preserves the natural cursor, metadata and
protected prefix. No memory image is needed for the next field's reads. -/
theorem current_step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (field : Field) (heap : BitVec 64) (position floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) (small : SmallField field)
    (headerFits : position+9<2^64) (positiveFloor : 0<floor) (aligned : floor%8=0)
    (afterFloor : floor≤position) (beforeHeap : floor≤heap.toNat)
    (normal : evaluateHOLFiniteState source (.seq (call field) advance)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤currentSize field ∧
      post.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (position+encoded)))) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<floor→post.memory query=source.memory query) ∧
      ∀ key : MlS,key≠ofString "p"→key≠ofString "w"→post.locals.lookup key=source.locals.lookup key := by
  obtain ⟨middle,called,advanced⟩:=sequence_none source post _ _ normal
  have positionNumber : (BitVec.ofNat 64 position).toNat=position:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨encoded,positive,upper,w,metadata,memory,others⟩:=current_call_normal source middle field (BitVec.ofNat 64 position) heap floor
    installed domain p heapCell lower bounded small (by rw [positionNumber]; exact headerFits) positiveFloor aligned
    (by rw [positionNumber]; exact afterFloor) beforeHeap called
  have pM : middle.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))):=(others _ (by decide)).trans p
  have read : eval middle advanceExpression=some (.val (.word (BitVec.ofNat 64 (position+encoded)))):=by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,pM,w,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint:=assign_none middle post "p" advanceExpression (BitVec.ofNat 64 (position+encoded)) read advanced
  rw [endpoint]
  refine ⟨encoded,positive,upper,bind_lookup_same _ _ _,metadata,memory,?_⟩
  intro key pNe wNe
  exact (show (bind middle "p" (BitVec.ofNat 64 (position+encoded))).locals.lookup key=middle.locals.lookup key from by
    simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,pNe,Ne.symm pNe]).trans (others key wNe)

end InitECandidate.Solver.Input.CurrentRlp.FieldWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.current_call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.current_call_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.FieldWrite.current_step_normal

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

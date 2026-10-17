import InitECandidate.Solver.Input.HeaderEncoding.FieldBounds

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem arguments_two (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (left right : ValueHOL 64)
    (readFirst : eval source first=some left) (readSecond : eval source second=some right) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [first,second]=some [left,right] := by
  simp only [eval] at readFirst readSecond
  simp only [evalListHOLFinite,evalListHOLExact,readFirst,readSecond]

theorem arguments_three (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second third : ExpHOL 64) (left middle right : ValueHOL 64)
    (readFirst : eval source first=some left) (readSecond : eval source second=some middle) (readThird : eval source third=some right) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [first,second,third]=some [left,middle,right] := by
  simp only [eval] at readFirst readSecond readThird
  simp only [evalListHOLFinite,evalListHOLExact,readFirst,readSecond,readThird]

/-- Each literal header field executes its actual writer, preserves the old
header cells, and pays its own encoded-size/source-clock allowance. -/
theorem field_run (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer old : BitVec 64)
    (field : Field) (position : Nat) (context : Context source original header buffer) (codes : Codes source)
    (facts : FieldFacts original header field) (positivePosition : 9≤position) (inside : position+maxSize field≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (w : source.locals.lookup (ofString "w")=some (.val (.word old))) (enough : maxCost field≤source.clock) :
    FieldRun source original buffer field := by
  classical
  have pRead : eval source (localVar "p")=some (.val (.word (address buffer position))) := by simp [eval,localVar,evalHOLExact,toExact,p]
  have positionNumber:=context.geometry.position_number header buffer position (by
    cases field <;> simp only [maxSize] at inside <;> omega)
  cases field with
  | bytes offset length=>
    obtain ⟨offsetBound,aligned,lengthBound,arena⟩:=facts
    have pointerRead:=context.load_one source original header buffer offset offsetBound aligned
    have args:=arguments_three source (localVar "p") (loadOne offset) (.const (BitVec.ofNat 64 length)) _ _ _ pRead pointerRead rfl
    exact bytes_field source original header buffer (wordAt original (address header offset)) old (.bytes offset length) position length _ context codes
      positivePosition inside lengthBound (by simp [maxSize]) (by simp [maxCost]) arena w args rfl enough
  | extra=>
    obtain ⟨lengthBound,arena⟩:=facts
    let length:=(wordAt original (address header 136)).toNat
    have pointerRead:=context.load_one source original header buffer 128 (by decide) (by decide)
    have rawRead:=context.load_one source original header buffer 136 (by decide) (by decide)
    have lengthRead : eval source (loadOne 136)=some (.val (.word (BitVec.ofNat 64 length))) := by simpa [length] using rawRead
    have args:=arguments_three source (localVar "p") (loadOne 128) (loadOne 136) _ _ _ pRead pointerRead lengthRead
    exact bytes_field source original header buffer (wordAt original (address header 128)) old .extra position length _ context codes
      positivePosition inside (by dsimp [length]; omega) (by change length+9≤41; dsimp [length]; omega)
      (by change length+21≤53; dsimp [length]; omega) arena w args rfl enough
  | scalar offset=>
    obtain ⟨offsetBound,aligned⟩:=facts
    have valueRead:=context.load_one source original header buffer offset offsetBound aligned
    have args:=arguments_two source (localVar "p") (loadOne offset) _ _ pRead valueRead
    have destination:=context.geometry.position_arena header buffer position 9 inside
    have mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (address buffer position+BitVec.ofNat 64 index)) := by
      intro index small
      exact WitnessRadix.AllocatedBytes.byte_mapped source (address buffer position) 9 index context.domain destination small
    obtain ⟨memory,encoded,paid,lower,upper,bound,run,frame⟩:=RlpWrite.WordWrite.assign_execute source (address buffer position) (wordAt original (address header offset)) old "w"
      [localVar "p",loadOne offset] w args codes.wordCode codes.u256Codes.bytesCodes.beCode codes.u256Codes.bytesCodes.put mapped enough
    have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
    refine ⟨memory,encoded,paid+1,lower,upper,by change paid+1≤19; omega,?_,?_⟩
    · change evaluateHOLFiniteState source (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") [localVar "p",loadOne offset])=_
      simpa only [subtract] using run
    · intro query before
      have away:=before_away (address buffer position) query 9 buffer.toNat destination (by omega) context.geometry.bufferAligned before
      exact (frame query (by intro index small; exact (away index small).2)).trans (context.oldMemory query before)
  | wide offset=>
    obtain ⟨offsetBound,aligned⟩:=facts
    have valueRead:=context.load_wide source original header buffer offset offsetBound aligned
    have args:=arguments_two source (localVar "p") (loadWide offset) _ _ pRead valueRead
    have destination:=context.geometry.position_arena header buffer position 41 inside
    have cursorNumber:=context.geometry.cursor_number header buffer
    have bufferArena:=context.geometry.buffer_arena header buffer
    have temporary : WitnessRadix.AllocatedBytes.Arena (cursor buffer) 32:=
      WitnessRadix.AllocatedBytes.Arena.subrange buffer 1056 1024 32 bufferArena (by decide)
    have cursorLower : 2701131776≤(cursor buffer).toNat := by rw [cursorNumber]; have h:=bufferArena.lower; omega
    have fits : (cursor buffer).toNat+32≤33806089496 := by rw [cursorNumber]; exact context.geometry.room
    obtain ⟨memory,encoded,paid,lower,upper,bound,number,run,frame⟩:=RlpWrite.U256Put.assign_execute source (wideWords original header offset)
      (address buffer position) (cursor buffer) old "w" [localVar "p",loadWide offset] w args codes.u256Code context.heap codes.u256Codes context.domain
        cursorLower fits destination enough
    have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
    refine ⟨memory,encoded,paid+1,lower,upper,by change paid+1≤125; omega,?_,?_⟩
    · change evaluateHOLFiniteState source (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_put_u256") [localVar "p",loadWide offset])=_
      simpa only [subtract] using run
    · intro query before
      have away:=before_away (address buffer position) query 41 buffer.toNat destination (by omega) context.geometry.bufferAligned before
      have tmpAway:=before_away (cursor buffer) query 32 buffer.toNat temporary (by omega) context.geometry.bufferAligned before
      exact (frame query away (by intro index small; exact (tmpAway index small).2)).trans (context.oldMemory query before)

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.arguments_two
#print axioms InitECandidate.Solver.Input.HeaderEncoding.arguments_three
#print axioms InitECandidate.Solver.Input.HeaderEncoding.field_run

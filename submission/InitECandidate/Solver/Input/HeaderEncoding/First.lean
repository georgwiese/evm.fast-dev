import InitECandidate.Solver.Input.HeaderEncoding.Rest

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The literal first writer declares w, advances p, and enters the remaining
fields. Its call is distinct from the later assignments to an existing w. -/
theorem after_pointer_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (context : Context source original header buffer)
    (codes : Codes source) (tailCodes : TailCodes source)
    (facts : ∀ field∈firstField::baseRest,FieldFacts original header field)
    (optionalFacts : wordAt original (address header 0)≠0#64→∀ field∈optionalFields,FieldFacts original header field)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer 9))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) (enough : 1344≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤1344 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source afterPointer=(some (.returned (encodedPair start encoded)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      OldMemory target.memory original buffer := by
  classical
  have firstFacts:=facts firstField (by simp)
  change 8≤240 ∧ 8%8=0 ∧ 32≤256 ∧ WitnessRadix.AllocatedBytes.Arena (wordAt original (address header 8)) 32 at firstFacts
  have pRead : eval source (localVar "p")=some (.val (.word (address buffer 9))) := by simp [eval,localVar,evalHOLExact,toExact,p]
  have pointerRead:=context.load_one source original header buffer 8 (by decide) (by decide)
  have args:=arguments_three source (localVar "p") (loadOne 8) (.const 32#64) _ _ _ pRead pointerRead rfl
  have destination:=context.geometry.position_arena header buffer 9 41 (by decide)
  obtain ⟨byte,access⟩:=RlpWrite.bytes_access source (address buffer 9) (wordAt original (address header 8)) 32 (by decide)
    context.domain firstFacts.2.2.2 destination
  obtain ⟨memory,firstEncoded,firstPaid,firstLower,firstPositive,firstUpper,firstBound,firstNumber,firstRun,memoryFrame⟩:=
    RlpWrite.BytesWrite.call_execute source (address buffer 9) (wordAt original (address header 8)) 32 byte "w" (arguments firstField) afterFirst
      args codes.u256Codes.bytesCode access codes.u256Codes.bytesCodes (by omega)
  have oldMemory : OldMemory memory original buffer := by
    intro query before
    have number:=context.geometry.position_number header buffer 9 (by decide)
    have away:=before_away (address buffer 9) query 41 buffer.toNat destination (by omega) context.geometry.bufferAligned before
    exact (memoryFrame query away).trans (context.oldMemory query before)
  let entered:=bind {source with memory:=memory,clock:=source.clock-1-firstPaid} "w" (BitVec.ofNat 64 firstEncoded)
  have pEntered : entered.locals.lookup (ofString "p")=some (.val (.word (address buffer 9))):=
    (bind_lookup_other _ "w" "p" _ (by decide)).trans p
  have wEntered : entered.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 firstEncoded))):=bind_lookup_same _ _ _
  have addRead : eval entered advanceExpression=some (.val (.word (address buffer (9+firstEncoded)))) := by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,pEntered,wEntered,valueIsWord,valueWord,wordOpHOL,wordOp,
      address,BitVec.ofNat_add,BitVec.add_assoc]
  let next:=fieldPost source memory buffer 9 firstEncoded (firstPaid+1)
  have subtract : source.clock-1-firstPaid=source.clock-(firstPaid+1) := by omega
  have advanceRun : evaluateHOLFiniteState entered advance=(none,next) := by
    have actual:=WitnessRadix.StateSteps.assign_execute entered "p" advanceExpression _ _ pEntered addRead
    change evaluateHOLFiniteState entered advance=(none,bind entered "p" (address buffer (9+firstEncoded))) at actual
    simpa only [entered,next,fieldPost,subtract] using actual
  have nextContext:=context.field_post source original memory header buffer 9 firstEncoded (firstPaid+1) oldMemory
  have nextLocals:=fieldPost_locals source memory buffer 9 firstEncoded (firstPaid+1)
  have nextBuf : next.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (fieldPost_other source memory buffer 9 firstEncoded (firstPaid+1) "buf" (by decide) (by decide)).trans buf
  obtain ⟨lastState,start,encoded,restPaid,positive,sizeBound,restBound,number,restRun,restFrame,lastMemory⟩:=
    rest_execute next original header buffer (BitVec.ofNat 64 firstEncoded) (9+firstEncoded) nextContext (Codes.of_code source next rfl codes)
      (TailCodes.of_code source next rfl tailCodes)
      (by intro field member; exact facts field (List.mem_cons_of_mem _ member)) optionalFacts (by omega) (by omega)
      nextLocals.1 nextLocals.2 nextBuf (by change 1291≤source.clock-(firstPaid+1); omega)
  have tailRun : evaluateHOLFiniteState entered afterFirst=(some (.returned (encodedPair start encoded)),lastState) := by
    rw [afterFirst,WitnessRadix.StateSteps.next_sequence entered next _ _ advanceRun (by change source.clock-(firstPaid+1)≤source.clock-1-firstPaid; omega)]
    exact restRun
  let target:=restore source "w" lastState
  let paid:=firstPaid+1+restPaid
  refine ⟨target,start,encoded,paid,positive,sizeBound,by dsimp [paid]; omega,number,?_,?_,lastMemory⟩
  · rw [afterPointer,firstRun,tailRun]
  · change emptyLocalsHOLFinite lastState=emptyLocalsHOLFinite {source with memory:=lastState.memory,clock:=source.clock-paid}
    change emptyLocalsHOLFinite lastState=emptyLocalsHOLFinite {source with memory:=lastState.memory,clock:=source.clock-(firstPaid+1)-restPaid} at restFrame
    have sub : source.clock-(firstPaid+1)-restPaid=source.clock-paid := by dsimp [paid]; omega
    simpa only [sub] using restFrame

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.after_pointer_execute

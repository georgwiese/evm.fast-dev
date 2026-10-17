import InitECandidate.Solver.Input.HeaderEncoding.Suffix

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem TailCodes.of_code (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : target.code=source.code) (codes : TailCodes source) : TailCodes target := by
  refine ⟨?_,?_,?_⟩
  all_goals rw [same]
  · exact codes.listLength
  · exact codes.headerLength
  · exact codes.listWriter

theorem rest_budgets : sizes baseRest=816 ∧ costs baseRest=1188 := by decide

/-- All fields following the first parent hash, the real optional guard and
the final list header compose into the actual remainder of encode_header. -/
theorem rest_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer old : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (codes : Codes source) (tailCodes : TailCodes source)
    (facts : ∀ field∈baseRest,FieldFacts original header field)
    (optionalFacts : wordAt original (address header 0)≠0#64→∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤50)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (w : source.locals.lookup (ofString "w")=some (.val (.word old)))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) (enough : 1291≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤1291 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (fields baseRest afterBase)=(some (.returned (encodedPair start encoded)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      OldMemory target.memory original buffer := by
  classical
  obtain ⟨middle,midPosition,midWord,basePaid,midLower,midUpper,baseBound,midContext,midState,midP,midW,midOthers,resume⟩:=
    fields_execute source original header buffer old baseRest position context codes facts lower
      (by rw [rest_budgets.1]; omega) p w (by rw [rest_budgets.2]; omega)
  rw [rest_budgets.1] at midUpper
  rw [rest_budgets.2] at baseBound
  have midClock:=congrArg PanSemStateFiniteExact.clock midState
  change middle.clock=source.clock-basePaid at midClock
  have midCode:=congrArg PanSemStateFiniteExact.code midState
  change middle.code=source.code at midCode
  have midBuf : middle.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (midOthers "buf" (by decide) (by decide)).trans buf
  obtain ⟨lastState,lastPosition,lastWord,optionalPaid,lastLower,lastUpper,optionalBound,lastContext,lastStateFrame,lastP,lastW,lastOthers,optionalRun⟩:=
    optional_guard_execute middle original header buffer midWord midPosition midContext (Codes.of_code source middle midCode codes)
      optionalFacts (by omega) (by omega) midP midW (by omega)
  have lastClock:=congrArg PanSemStateFiniteExact.clock lastStateFrame
  change lastState.clock=middle.clock-optionalPaid at lastClock
  have lastCode:=congrArg PanSemStateFiniteExact.code lastStateFrame
  change lastState.code=middle.code at lastCode
  have lastBuf : lastState.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (lastOthers "buf" (by decide) (by decide)).trans midBuf
  obtain ⟨target,start,encoded,suffixPaid,positive,sizeBound,suffixBound,number,suffixRun,suffixFrame,memoryFrame⟩:=
    suffix_execute lastState original header buffer lastPosition lastContext (Codes.of_code source lastState (lastCode.trans midCode) codes)
      (TailCodes.of_code source lastState (lastCode.trans midCode) tailCodes) (by omega) (by omega) lastP lastBuf (by omega)
  let paid:=basePaid+optionalPaid+suffixPaid
  refine ⟨target,start,encoded,paid,positive,sizeBound,by dsimp [paid]; omega,number,?_,?_,memoryFrame⟩
  · rw [resume,afterBase,WitnessRadix.StateSteps.next_sequence middle lastState _ _ optionalRun (by omega)]
    exact suffixRun
  · rw [lastStateFrame,midState] at suffixFrame
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-basePaid-optionalPaid-suffixPaid} at suffixFrame
    have subtract : source.clock-basePaid-optionalPaid-suffixPaid=source.clock-paid := by dsimp [paid]; omega
    simpa only [subtract] using suffixFrame

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.TailCodes.of_code
#print axioms InitECandidate.Solver.Input.HeaderEncoding.rest_budgets
#print axioms InitECandidate.Solver.Input.HeaderEncoding.rest_execute

import InitECandidate.Solver.Input.HeaderEncoding.Fields

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The exact optional pair terminates in its literal final p assignment,
including both actual writer calls and the old-header memory invariant. -/
theorem optional_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer old : BitVec 64)
    (position : Nat) (context : Context source original header buffer) (codes : Codes source)
    (facts : ∀ field∈optionalFields,FieldFacts original header field)
    (positivePosition : 9≤position) (inside : position+50≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (w : source.locals.lookup (ofString "w")=some (.val (.word old))) (enough : 72≤source.clock) :
    ∃ target finalPosition last paid,position≤finalPosition ∧ finalPosition≤position+50 ∧ paid≤72 ∧
      Context target original header buffer ∧ target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "p")=some (.val (.word (address buffer finalPosition))) ∧
      target.locals.lookup (ofString "w")=some (.val (.word last)) ∧
      (∀ name : String,ofString "p"≠ofString name→ ofString "w"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      evaluateHOLFiniteState source optionalCode=(none,target) := by
  classical
  obtain ⟨middle,midPosition,midWord,firstPaid,midLower,midUpper,firstBound,midContext,midState,midP,midW,midOthers,resume⟩:=
    fields_execute source original header buffer old [.bytes 232 32] position context codes
      (by intro field member; simp only [List.mem_singleton] at member; subst field; exact facts _ (by simp [optionalFields]))
      positivePosition (by change position+41≤1024; omega) p w (by change 53≤source.clock; omega)
  change midPosition≤position+41 at midUpper
  change firstPaid≤53 at firstBound
  have midClock:=congrArg PanSemStateFiniteExact.clock midState
  change middle.clock=source.clock-firstPaid at midClock
  have midCode:=congrArg PanSemStateFiniteExact.code midState
  change middle.code=source.code at midCode
  have midCodes:=Codes.of_code source middle midCode codes
  obtain ⟨memory,encoded,lastPaid,lower,upper,lastBound,run,oldFrame⟩:=field_run middle original header buffer midWord (.scalar 240) midPosition midContext midCodes
    (facts _ (by simp [optionalFields])) (by omega) (by change midPosition+9≤1024; omega) midP midW (by change 19≤middle.clock; omega)
  change encoded≤9 at upper
  change lastPaid≤19 at lastBound
  let target:=fieldPost middle memory buffer midPosition encoded lastPaid
  have targetContext:=midContext.field_post middle original memory header buffer midPosition encoded lastPaid oldFrame
  have targetLocals:=fieldPost_locals middle memory buffer midPosition encoded lastPaid
  have actual : evaluateHOLFiniteState source optionalCode=(none,target) := by
    rw [optionalCode,resume]
    exact (assemble_field middle memory buffer (.scalar 240) midPosition encoded lastPaid midP run).1
  refine ⟨target,midPosition+encoded,BitVec.ofNat 64 encoded,firstPaid+lastPaid,by omega,by omega,by omega,targetContext,?_,targetLocals.1,targetLocals.2,?_,actual⟩
  · have targetState : target={middle with locals:=target.locals,memory:=memory,clock:=middle.clock-lastPaid}:=rfl
    rw [midState] at targetState
    change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-firstPaid-lastPaid} at targetState
    have subtract : source.clock-firstPaid-lastPaid=source.clock-(firstPaid+lastPaid) := by omega
    simpa only [subtract] using targetState
  · intro name pNe wNe
    exact (fieldPost_other middle memory buffer midPosition encoded lastPaid name pNe wNe).trans (midOthers name pNe wNe)

/-- Actual current-header guard, including its genuine skipped branch. -/
theorem optional_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer old : BitVec 64)
    (position : Nat) (context : Context source original header buffer) (codes : Codes source)
    (facts : wordAt original (address header 0)≠0#64→∀ field∈optionalFields,FieldFacts original header field)
    (positivePosition : 9≤position) (inside : position+50≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (w : source.locals.lookup (ofString "w")=some (.val (.word old))) (enough : 72≤source.clock) :
    ∃ target finalPosition last paid,position≤finalPosition ∧ finalPosition≤position+50 ∧ paid≤72 ∧
      Context target original header buffer ∧ target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "p")=some (.val (.word (address buffer finalPosition))) ∧
      target.locals.lookup (ofString "w")=some (.val (.word last)) ∧
      (∀ name : String,ofString "p"≠ofString name→ ofString "w"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      evaluateHOLFiniteState source (.ite currentTest optionalCode .skip)=(none,target) := by
  classical
  have read:=context.load_one source original header buffer 0 (by decide) (by decide)
  have testRead : eval source currentTest=some (.val (.word (if wordAt original (address header 0)=0#64 then 0#64 else 1#64))) := by
    simp only [eval] at read ⊢
    rw [currentTest,evalHOLExact,read]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at testRead
  by_cases zero : wordAt original (address header 0)=0#64
  · refine ⟨source,position,old,0,by omega,by omega,by omega,context,by simp,p,w,by intros; rfl,?_⟩
    rw [evaluateHOLFiniteState_ite,testRead]
    simp [zero]
  · obtain ⟨target,finalPosition,last,paid,lower,upper,bound,targetContext,frame,finalP,finalW,others,run⟩:=
      optional_execute source original header buffer old position context codes (facts zero) positivePosition inside p w enough
    refine ⟨target,finalPosition,last,paid,lower,upper,bound,targetContext,frame,finalP,finalW,others,?_⟩
    rw [evaluateHOLFiniteState_ite,testRead]
    simpa [zero] using run

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.Codes.of_code
#print axioms InitECandidate.Solver.Input.HeaderEncoding.optional_execute
#print axioms InitECandidate.Solver.Input.HeaderEncoding.optional_guard_execute

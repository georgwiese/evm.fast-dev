import InitECandidate.Solver.Input.VerifyProgram

namespace InitECandidate.Solver.Input.Verify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real verify wrapper reaches attempt_l7 after two literal local
initializations and one caller tick; its catch/return tail preserves the
actual child's final clock on all outcomes. -/
theorem trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry childPost childResult,
      entry.locals.lookup (ofString "si")=some (.val (.word si)) ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      entry.clock=source.clock-1 ∧ evaluateHOLFiniteState entry AttemptWrapper.Kind.evm.body=(childResult,childPost) ∧ childPost.clock=post.clock := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · let current:=declared source
    have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)) :=
      (bind_lookup_other (bind source "e" 0#64) "ok" "si" 1#64 (by decide)).trans
        ((bind_lookup_other source "e" "si" 0#64 (by decide)).trans binding)
    have code : current.code.lookup (ofString "attempt_l7")=some (formals,AttemptWrapper.Kind.evm.body,.one) := by
      exact AttemptWrapper.original_code .evm source.code installed
    obtain ⟨callee,called,siCell⟩ := word_environment current.code.lookup (ofString "attempt_l7") (ofString "si") AttemptWrapper.Kind.evm.body .one si code
    have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) arguments=some [.val (.word si)] := by
      simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentSi]
    have actualCall:=CallNormal.ignored_handled_clock current (ofString "attempt_l7") (ofString "Fail") (ofString "e") arguments _ AttemptWrapper.Kind.evm.body handler callee .one args called zero handler_clock
    change (evaluateHOLFiniteState current call).2.clock=(evaluateHOLFiniteState (callEntryStateHOLFinite current callee) AttemptWrapper.Kind.evm.body).2.clock at actualCall
    have clock:=body_clock source
    rw [run] at clock
    let entry:=callEntryStateHOLFinite current callee
    let childPost:=(evaluateHOLFiniteState entry AttemptWrapper.Kind.evm.body).2
    let childResult:=(evaluateHOLFiniteState entry AttemptWrapper.Kind.evm.body).1
    exact Or.inr ⟨entry,childPost,childResult,siCell,rfl,rfl,rfl,(clock.trans actualCall).symm⟩

/-- Complete original verify/attempt chain: stop within eight caller ticks,
or derive the actual unchanged run_attempt815 entry with every nonlocal
field preserved and the real final-clock relation. -/
theorem to_run (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤8 ∨ AttemptWrapper.Reaches source post si 8 := by
  rcases trace source post si installed binding outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨entry,childPost,childResult,entrySi,frame,clock,childRun,finalClock⟩ := reached
    have entryCode:=congrArg PanSemStateFiniteExact.code frame
    change entry.code=source.code at entryCode
    have entryInstalled : OriginalCode.Installed entry.code := by rw [entryCode]; exact installed
    rcases AttemptWrapper.to_run .evm entry childPost si entryInstalled entrySi childResult childRun with stopped|continued
    · have forward:=evaluateHOLFiniteState_clock_le entry AttemptWrapper.Kind.evm.body
      rw [childRun] at forward
      change entry.clock-childPost.clock≤7 at stopped
      exact Or.inl (by omega)
    · obtain ⟨last,target,result,lastSi,lastFrame,lastClock,lastRun,endpoint⟩ := continued
      refine Or.inr ⟨last,target,result,lastSi,lastFrame.trans frame,?_,lastRun,endpoint.trans finalClock⟩
      change last.clock=entry.clock-7 at lastClock
      rw [clock] at lastClock
      omega

end InitECandidate.Solver.Input.Verify

#print axioms InitECandidate.Solver.Input.Verify.trace
#print axioms InitECandidate.Solver.Input.Verify.to_run

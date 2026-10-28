import InitECandidate.Solver.Input.AttemptWrapperProgram
import InitECandidate.Solver.Input.HandledCallClock
import InitECandidate.Solver.Input.QuietHandlerClock
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.AttemptWrapper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def declared (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "e" 0#64

theorem handler_clock (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source kind.handler).2.clock=source.clock := by
  unfold Kind.handler
  exact QuietClock.sequence source.code _ _ (QuietClock.shared_store source.code _ _ _) (QuietClock.raised source.code _ _) source rfl

/-- The original declaration and final return do not change the actual
child call's final clock, on normal or escaping exceptional outcomes. -/
theorem body_clock (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source kind.body).2.clock=(evaluateHOLFiniteState (declared source) kind.call).2.clock := by
  let tail:=ProgHOL.seq kind.call (.return (.const 0#64))
  let output:=evaluateHOLFiniteState (declared source) tail
  have actual:=ScalarScope.declare_execute source output.2 "e" (.const 0#64) 0#64 tail output.1 rfl rfl
  have projected:=congrArg (fun result=>result.2.clock) actual
  rw [body_shape]
  change (evaluateHOLFiniteState source (.dec (ofString "e") .one (.const 0#64) tail)).2.clock=_
  rw [projected]
  change (evaluateHOLFiniteState (declared source) tail).2.clock=_
  exact QuietClock.sequence_clock (declared source) kind.call (.return (.const 0#64))
    (fun current=>QuietClock.returned current.code _ current rfl)

/-- Every funded original wrapper exposes its genuine child entry/run.
Only real local/clock changes precede it; the handler/return tail retains
the child's actual final clock on every outcome. -/
theorem trace (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64) (childBody : ProgHOL 64)
    (binding : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (childCode : source.code.lookup kind.child=some (formals,childBody,.one))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.body=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry childPost childResult,
      entry.locals.lookup (ofString "si")=some (.val (.word si)) ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      entry.clock=source.clock-1 ∧ evaluateHOLFiniteState entry childBody=(childResult,childPost) ∧ childPost.clock=post.clock := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · let current:=declared source
    have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)) :=
      (bind_lookup_other source "e" "si" 0#64 (by decide)).trans binding
    obtain ⟨callee,called,siCell⟩ := word_environment current.code.lookup kind.child (ofString "si") childBody .one si childCode
    have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) arguments=some [.val (.word si)] := by
      simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentSi]
    have actualCall:=CallNormal.ignored_handled_clock current kind.child kind.exception (ofString "e") arguments _ childBody kind.handler callee .one args called zero (handler_clock kind)
    change (evaluateHOLFiniteState current kind.call).2.clock=(evaluateHOLFiniteState (callEntryStateHOLFinite current callee) childBody).2.clock at actualCall
    have clock:=body_clock kind source
    rw [run] at clock
    let entry:=callEntryStateHOLFinite current callee
    let childPost:=(evaluateHOLFiniteState entry childBody).2
    let childResult:=(evaluateHOLFiniteState entry childBody).1
    exact Or.inr ⟨entry,childPost,childResult,siCell,rfl,rfl,rfl,(clock.trans actualCall).symm⟩

end InitECandidate.Solver.Input.AttemptWrapper

#print axioms InitECandidate.Solver.Input.AttemptWrapper.handler_clock
#print axioms InitECandidate.Solver.Input.AttemptWrapper.body_clock
#print axioms InitECandidate.Solver.Input.AttemptWrapper.trace

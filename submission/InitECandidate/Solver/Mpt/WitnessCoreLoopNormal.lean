import InitECandidate.Solver.Mpt.WitnessCoreLoopBound
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.WhileNormalGuard

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A genuine normal exit has really read go=0. The reachable stopped
shape has an empty physical stack, returning mode, a typed result and
owned header/cache words, with both original databases still frozen. -/
theorem Invariant.loop_normal (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant input frontier db limit source configuration)
    (normal : evaluateHOLFiniteState source (.while WitnessCore.condition loopBody)=(none,post)) :
    ∃ heap cursor child,
      Invariant input frontier db limit post ⟨heap,cursor,[],.returning,false⟩ ∧
      post.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "result")=some (.val (.word child)) ∧
      ResultOwned post (resultLower []) heap.toNat child := by
  have step (current : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : current.code=source.code)
      (valid : Valid input frontier db limit current) (word : BitVec 64)
      (guard : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) WitnessCore.condition=some (.val (.word word)))
      (nonzero : word≠0) (funded : current.clock≠0) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,target)) : Valid input frontier db limit target := by
    obtain ⟨rank,actual,ready,rankEq⟩:=valid
    have read:=ready.condition input frontier db limit current actual
    have same : goWord actual.running=word:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans guard)))
    have running : actual.running=true:=by
      cases observed : actual.running with
      | false=>
        apply False.elim
        apply nonzero
        rw [←same,observed]
        rfl
      | true=>rfl
    have nextReady:=ready.dec_clock input frontier db limit current actual
    obtain ⟨next,nextInvariant,smaller⟩:=nextReady.body_normal input frontier db limit (decClockHOLFinite current) target actual running run
    exact ⟨next.rank limit,next,nextInvariant,rfl⟩
  have valid : Valid input frontier db limit source:=⟨configuration.rank limit,configuration,invariant,rfl⟩
  have final:=Input.loop_invariant source.code (Flapjack.Basis.Pure.MlString.ofString "db") WitnessCore.condition loopBody loop_body_prefix
    (Valid input frontier db limit) step source post rfl valid normal
  obtain ⟨rank,actual,finished,rankEq⟩:=final
  have falseGuard:=Input.while_normal_guard WitnessCore.condition loopBody
    (fun current=>(loop_body_prefix.summary_full current).2.2) source post normal
  have read:=finished.condition input frontier db limit post actual
  have zero : goWord actual.running=0#64:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans falseGuard)))
  have stopped : actual.running=false:=by
    cases observed : actual.running with
    | false=>rfl
    | true=>
      have impossible : (1#64 : BitVec 64)=0#64:=by simpa only [goWord,observed,ite_true] using zero
      exact False.elim ((by decide : (1#64 : BitVec 64)≠0#64) impossible)
  have shape:=finished.stopped.resolve_left (by rw [stopped]; decide)
  obtain ⟨emptyStack,returning⟩:=shape
  rcases actual with ⟨heap,cursor,stack,phase,running⟩
  change stack=[] at emptyStack
  change phase=.returning at returning
  change running=false at stopped
  subst stack
  subst phase
  subst running
  obtain ⟨waiting,child,result,owned⟩:=finished.phase
  exact ⟨heap,cursor,child,finished,result,owned⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.loop_normal

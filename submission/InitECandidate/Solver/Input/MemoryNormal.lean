import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.LoopSummaryInvariant

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Lift a genuine normal callee's protected word through its real ignored
caller. Exact arguments/lookup identify the callee in that same invocation. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (query : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (frame : ∀ target value,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target) → target.memory query=source.memory query)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post function arguments run
  have valuesEq : actualValues=values := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,shape) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have same := frame target returned bodyRun
  rw [endpoint]
  exact same

/-- Compose actual normal-prefix and returning-suffix word frames. -/
theorem sequence_returned {F : Type} (source post : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64) (query : BitVec 64)
    (never : ∀ value,(evaluateHOLFiniteState source first).1≠some (.returned value))
    (front : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → middle.memory query=source.memory query)
    (back : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → ∀ value,
      evaluateHOLFiniteState middle second=(some (.returned value),post) → post.memory query=middle.memory query)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq first second)=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post first second value never run
  exact (back middle normal value remaining).trans (front middle normal)

/-- A known scalar declaration restores only locals after the actual
returning body, so a protected memory word passes through its scope. -/
theorem declaration_returned {F : Type} (source post : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word query : BitVec 64) (body : ProgHOL 64) (value : ValueHOL 64)
    (read : eval source expression=some (.val (.word word)))
    (frame : ∀ inner,evaluateHOLFiniteState (bind source name word) body=(some (.returned value),inner) → inner.memory query=source.memory query)
    (run : evaluateHOLFiniteState source (.dec (ofString name) .one expression body)=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨inner,remaining,endpoint⟩ := declaration_return_word source post name expression word body value read run
  rw [endpoint]
  exact frame inner remaining

/-- A real normal loop preserves a word when its actual continuing bodies
preserve it while deriving their next current invariant. -/
theorem loop_normal (code) (key : MlS) (condition : ExpHOL 64) (body : ProgHOL 64) (query : BitVec 64)
    (safe : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key body current)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory→Prop)
    (step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target) → invariant target ∧ target.memory query=current.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : source.code=code) (ready : invariant source)
    (run : evaluateHOLFiniteState source (.while condition body)=(none,post)) : post.memory query=source.memory query := by
  have preserved := loop_invariant_summary code key condition body safe (fun current=>invariant current ∧ current.memory query=source.memory query)
    (by intro current installed actual word read nonzero funded target bodyRun
        have next := step current installed actual.1 word read nonzero funded target bodyRun
        exact ⟨next.1,next.2.trans actual.2⟩) source post codeEq ⟨ready,rfl⟩ run
  exact preserved.2

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.call_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.sequence_returned
#print axioms InitECandidate.Solver.Input.MemoryAt.declaration_returned
#print axioms InitECandidate.Solver.Input.MemoryAt.loop_normal

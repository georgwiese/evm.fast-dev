import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Releasing a heap mark changes a global, never ordinary memory, on any
outcome, including malformed current locals or globals. -/
theorem release_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source releaseBody).2.memory=source.memory := by
  rw [release_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign]
  repeat first | rfl | split | rw [evaluateHOLFiniteState_return]
  all_goals simp [evaluateHOLFiniteState_return,setKvarHOLFinite,setGlobalHOLFinite,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,emptyLocalsHOLFinite]

/-- A genuine normal ignored release retains memory without requiring a
future mark value, valid argument model or a successful helper premise. -/
theorem ignored_release_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") arguments)=(none,post)) :
    post.memory=source.memory := by
  obtain ⟨positive,values,body,callee,shape,target,returned,args,called,bodyRun,checked,postEq,fields⟩ :=
    CallNormal.ignored_data source post (ofString "heap_release") arguments normal
  have bodyEq := LocalEffects.lookup_body source.code (ofString "heap_release") releaseFormals releaseBody .one
    (release_original_code source.code installed) values body callee shape called
  subst body
  have memory := release_memory (callEntryStateHOLFinite source callee)
  rw [bodyRun] at memory
  rw [postEq]
  exact memory

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.release_memory
#print axioms InitECandidate.Solver.Input.HeapScope.ignored_release_memory

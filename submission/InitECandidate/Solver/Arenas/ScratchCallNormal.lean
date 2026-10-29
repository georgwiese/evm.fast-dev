import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Arenas.Scratch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem release_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word mark)])
    (cursor : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word old)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "scratch_release") arguments)=(none,post)) :
    1≤source.clock ∧ post=released {source with clock:=source.clock-1} mark := by
  obtain ⟨callee,called,m⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "scratch_release") "m" releaseBody mark (release_code source.code installed)
  have positive := (Input.CallNormal.ignored_callee_return source post (ofString "scratch_release") arguments _ releaseBody callee .one args called normal).1
  let entry := callEntryStateHOLFinite source callee
  have bodyRun := release_execute entry mark old m cursor
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "scratch_release") arguments [.val (.word mark)] releaseBody callee .one
    (.val (.word 0#64)) (emptyLocalsHOLFinite (released entry mark)) args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  rw [actual] at normal
  exact ⟨positive,(Prod.mk.inj normal).2.symm⟩

/-- Releasing the genuine unchanged mark restores the same physical state.
Only the actual caller clock is paid. -/
theorem release_same_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word mark)])
    (cursor : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word mark)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "scratch_release") arguments)=(none,post)) :
    post={source with clock:=source.clock-1} := by
  obtain ⟨funded,endpoint⟩:=release_call_normal source post mark mark arguments args cursor installed normal
  have globals : source.globals.update (ofString "scratch_ptr",.val (.word mark))=source.globals := by
    apply HolFiniteMapExact.ext
    funext key
    simp only [HolFiniteMapExact.lookup_update_pointwise]
    by_cases same : key=ofString "scratch_ptr"
    · subst key
      exact cursor.symm
    · simp [same]
  simpa only [released,globals] using endpoint

end InitECandidate.Solver.Arenas.Scratch

#print axioms InitECandidate.Solver.Arenas.Scratch.release_call_normal
#print axioms InitECandidate.Solver.Arenas.Scratch.release_same_call_normal

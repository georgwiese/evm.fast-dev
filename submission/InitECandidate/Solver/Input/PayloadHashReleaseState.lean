import InitECandidate.Solver.Input.PayloadHashStateCall
import InitECandidate.Solver.Input.HeapReleaseNormal
import InitECandidate.Solver.Input.HeapReleaseMemory

namespace InitECandidate.Solver.Input.PayloadHash.ReleasePhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def call : ProgHOL 64 := .call (some (none,none)) (ofString "heap_release") [localVar "m2"]

theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source call=(result,post)) : source.clock-post.clock≤1 := by
  have price := HeapScope.release_call_cost source.code installed (some none) [localVar "m2"] source rfl
  change source.clock-(evaluateHOLFiniteState source call).2.clock≤1 at price
  rw [run] at price
  exact price

/-- Real original m2 release restores its actual saved cursor while retaining
all caller bindings and copied/decoded input agreement. -/
theorem call_normal (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor nextCursor mark stp accel chunk zeros : BitVec 64)
    (actual : StaticFields.State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (saved : source.locals.lookup (ofString "m2")=some (.val (.word nextCursor)))
    (run : evaluateHOLFiniteState source call=(none,post)) : StaticFields.State origin post lower upper pl raw ch out nextCursor mark stp accel chunk zeros := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "m2"]=some [.val (.word nextCursor)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,saved]
  have released := HeapScope.release_normal source post nextCursor cursor [localVar "m2"] args actual.ready.heap actual.ready.workspace.sha.installed run
  have heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextCursor)) := by
    rw [released]
    simp [HeapScope.releasePost,HolFiniteMapExact.lookup_update,FUPDATE]
  apply actual.after_program origin source post lower upper pl raw ch out cursor nextCursor mark stp accel chunk zeros call run heap
  · intro key different
    exact GlobalEffects.call_body key source.code (some none) (ofString "heap_release") [localVar "m2"] HeapScope.releaseFormals HeapScope.releaseBody .one
      (HeapScope.release_original_code source.code actual.ready.workspace.sha.installed) (Merkle.release_globals key source.code different)
  · intro name different
    exact CallNormal.ignored_lookup source post (ofString name) (ofString "heap_release") [localVar "m2"] run
  · intro query low high
    exact HeapScope.release_call_memory source post [localVar "m2"] query actual.ready.workspace.sha.installed run

end InitECandidate.Solver.Input.PayloadHash.ReleasePhase

#print axioms InitECandidate.Solver.Input.PayloadHash.ReleasePhase.call_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.ReleasePhase.call_normal

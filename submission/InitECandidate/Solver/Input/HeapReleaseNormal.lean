import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A genuine normal original release derives its own caller funding and
exact current global update, retaining the actual caller locals/memory. -/
theorem release_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word mark)])
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") arguments)=(none,post)) :
    post=releasePost {source with clock:=source.clock-1} mark := by
  have funded := (CallNormal.ignored_data source post (ofString "heap_release") arguments normal).1
  have actual := release_call_execute source mark old arguments args heap (release_original_code source.code installed) funded
  rw [normal] at actual
  exact congrArg Prod.snd actual

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.release_normal

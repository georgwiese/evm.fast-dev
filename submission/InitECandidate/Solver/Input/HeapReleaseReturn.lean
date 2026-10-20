import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal original heap_release/return suffix restores the actual
saved mark. Caller funding and the release result follow from that same
execution, without a future successful helper premise. -/
theorem release_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64)))=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨released,normal,returned⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
  have funded := (CallNormal.ignored_data source released (ofString "heap_release") [localVar "mark"] normal).1
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,saved]
  have actual := release_call_execute source mark old [localVar "mark"] args heap (release_original_code source.code installed) funded
  rw [normal] at actual
  have releaseEq : released=releasePost {source with clock:=source.clock-1} mark := congrArg Prod.snd actual
  have actualReturn : evaluateHOLFiniteState released (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite released) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  rw [actualReturn] at returned
  have postEq : post=emptyLocalsHOLFinite released := (congrArg Prod.snd returned).symm
  rw [postEq]
  change released.globals.lookup (ofString "heap_ptr")=_
  rw [releaseEq]
  simp [releasePost,HolFiniteMapExact.lookup_update,FUPDATE]

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.release_return_heap

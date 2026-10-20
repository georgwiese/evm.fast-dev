import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem ignored_never (function : MlS) (arguments : List (ExpHOL 64)) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) :
    (evaluateHOLFiniteState source (.call (some (none,none)) function arguments)).1≠some (.returned value) :=
  ((LocalPrefix.call (key:=ofString "mark") none function arguments (by intro name impossible; cases impossible)).summary_full source).2.1 value

/-- A real normal output suffix executes the original release with the
saved mark. Normality derives its funding; no successful release is assumed. -/
theorem copy_release_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memcpy") arguments) (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))))=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨copied,copyRun,remaining⟩ := sequence_returned source post _ _ value (ignored_never _ _ source) run
  have copyLocals := (LocalPrefix.call (key:=ofString "mark") none (ofString "memcpy") arguments (by intro name impossible; cases impossible)).summary_full source
  unfold LocalSummary at copyLocals
  simp only [Option.map_none] at copyLocals
  rw [copyRun] at copyLocals
  have copiedMark : copied.locals.lookup (ofString "mark")=some (.val (.word mark)) := (copyLocals.1 rfl).trans saved
  have copyGlobals := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memcpy") arguments
    CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code source.code installed) (Copy32.globals (ofString "heap_ptr") source.code) source rfl
  change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2=GlobalEffects.erase (ofString "heap_ptr") source at copyGlobals
  rw [copyRun] at copyGlobals
  have copiedHeap : copied.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) := (congrArg Prod.snd copyGlobals).trans heap
  have fields := evaluation_fields source copied _ none copyRun
  have copiedInstalled : OriginalCode.Installed copied.code := fields.2.2.2.symm ▸ installed
  obtain ⟨released,releaseRun,returned⟩ := sequence_returned copied post _ _ value (ignored_never _ _ copied) remaining
  have funded := (CallNormal.ignored_data copied released (ofString "heap_release") [localVar "mark"] releaseRun).1
  have args : evalListHOLFinite copied (h:=fun address=>Classical.propDecidable (copied.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,copiedMark]
  have actual := HeapScope.release_call_execute copied mark old [localVar "mark"] args copiedHeap
    (HeapScope.release_original_code copied.code copiedInstalled) funded
  rw [releaseRun] at actual
  have endpoint : released=HeapScope.releasePost {copied with clock:=copied.clock-1} mark := congrArg Prod.snd actual
  have postEq : post=emptyLocalsHOLFinite released := by
    have actualReturn : evaluateHOLFiniteState released (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite released) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact ]
    rw [actualReturn] at returned
    exact (congrArg Prod.snd returned).symm
  rw [postEq]
  change released.globals.lookup (ofString "heap_ptr")=_
  rw [endpoint]
  simp [HeapScope.releasePost,HolFiniteMapExact.lookup_update,FUPDATE]

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.copy_release_return_heap

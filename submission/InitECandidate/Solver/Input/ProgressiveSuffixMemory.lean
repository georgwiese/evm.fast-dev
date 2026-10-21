import InitECandidate.Solver.Input.ProgressiveFoldMemory
import InitECandidate.Solver.Input.CopyReturnMemory
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.ProgressiveLoopMemory

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out query : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel)
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32)
    (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterFold=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outputArguments=some (CopyGeneral.values out acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,outputArguments,localVar,accumulator,output,CopyGeneral.values]
  rw [fold_shape.2.2.2.2.2] at run
  exact MemoryAt.copy_release_returned source post outputArguments [localVar "mark"] acc out query 32 workspace.installed workspace.domain args accArena outArena outAway value run

/-- Actual final zero, bounded root fold, output copy and release preserve
one input/decoded word outside their real buffers. -/
theorem suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (roots acc out stp accel query : BitVec 64) (k : Nat) (inside : k≤15)
    (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32)
    (outArena : AllocatedBytes.Arena out 32) (aligned : acc.toNat%8=0)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96)
    (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [fold_shape.2.2.2.1] at run
  have zeroSafe : LocalPrefix (ofString "acc") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,zeroRun,remaining⟩ := Input.sequence_returned source post _ afterZeroAcc value (zeroSafe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,accumulator,Zero.values]
  have zeroMemory := MemoryAt.zero_normal source middle zeroArguments acc query 32 args workspace.installed workspace.domain accArena aligned (by decide) (fun offset bound=>(accAway offset bound).1) zeroRun
  have zeroGlobals (key : MlS) : GlobalEffects.Preserves key source.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
    GlobalEffects.call_body key source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code workspace.installed) (Zero.globals key source.code)
  have middleWorkspace := ShaPair.Workspace.after source middle stp accel workspace _ none zeroRun (zeroGlobals (ofString "sha_st")) (zeroGlobals (ofString "sha_accel"))
  have middleOther (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source middle (ofString name) (ofString "memzero") zeroArguments zeroRun
  rw [fold_shape.2.2.2.2.1] at remaining
  obtain ⟨final,foldRun,outputRun⟩ := Input.sequence_returned middle post foldLoop afterFold value ((fold_loop_other (ofString "acc") (by decide)).summary_full middle).2.1 remaining
  have foldMemory := fold_loop_memory middle final roots acc stp accel query k inside middleWorkspace
    ((middleOther "roots").trans root) ((middleOther "acc").trans accumulator) ((middleOther "k").trans round)
    rootsArena accArena stateAway accelAway accAway foldRun
  have finalWorkspace := ShaPair.Workspace.after middle final stp accel middleWorkspace foldLoop none foldRun
    (fold_loop_globals (ofString "sha_st") middle.code middleWorkspace.installed) (fold_loop_globals (ofString "sha_accel") middle.code middleWorkspace.installed)
  have finalOther (name : String) (different : ofString name≠ofString "k") : final.locals.lookup (ofString name)=middle.locals.lookup (ofString name) := by
    have summary := (fold_loop_other (ofString name) different).summary_full middle
    unfold LocalSummary at summary
    rw [foldRun] at summary
    exact summary.1 rfl
  have outputMemory := output_memory final post acc out query finalWorkspace
    (((finalOther "acc" (by decide)).trans (middleOther "acc")).trans accumulator)
    (((finalOther "out" (by decide)).trans (middleOther "out")).trans output) accArena outArena outAway value outputRun
  exact outputMemory.trans (foldMemory.trans zeroMemory)

/-- Whole actual progressive loop and suffix share the same protected
word, with all post-loop facts derived from the observed normal loop. -/
theorem dense_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor zeros stp accel chunk acc out query : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k)
    (protection : SszHash.Protected source stp accel chunk zeros query) (mapped : Geometry p roots cursor zeros n)
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) (aligned : acc.toNat%8=0)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query 768)
    (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [fold_shape.2.2.1] at run
  have safe : LocalPrefix (ofString "acc") loop := by rw [loop_shape.1]; exact .loop _ (step_other (ofString "acc") (by decide) (by decide) (by decide) (by decide))
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post loop afterLoop value (safe.summary_full source).2.1 run
  have front := loop_memory source middle p roots cursor zeros stp accel chunk query n k bounded inside actual protection mapped below rootsAway normal
  obtain ⟨position,positionBound,current⟩ := loop_normal source middle p roots cursor zeros stp accel n k bounded inside actual mapped normal
  have other (name : String) (a : ofString name≠ofString "cnt") (b : ofString name≠ofString "off") (c : ofString name≠ofString "size") (d : ofString name≠ofString "k") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) loop := by rw [loop_shape.1]; exact .loop _ (step_other (ofString name) a b c d)
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact (suffix_memory middle post roots acc out stp accel query position positionBound current.workspace current.rootsLocal
    ((other "acc" (by decide) (by decide) (by decide) (by decide)).trans accumulator)
    ((other "out" (by decide) (by decide) (by decide) (by decide)).trans output) current.round mapped.rootsArena accArena outArena aligned
    protection.stateAway protection.accelAway accAway outAway value remaining).trans front

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.output_memory
#print axioms InitECandidate.Solver.Input.Progressive.suffix_memory
#print axioms InitECandidate.Solver.Input.Progressive.dense_memory

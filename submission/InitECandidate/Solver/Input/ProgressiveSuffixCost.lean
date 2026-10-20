import InitECandidate.Solver.Input.ProgressiveFoldCost
import InitECandidate.Solver.Input.HeapCopyRelease

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem fold_loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code foldLoop := by
  rw [fold_shape.1]
  exact GlobalEffects.loop key code _ _ (fold_globals key code installed)

theorem fold_loop_other (key : MlS) (different : key≠ofString "k") : LocalPrefix key foldLoop := by
  rw [fold_shape.1]
  exact LocalPrefix.loop _ (fold_other key different)

theorem output_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel)
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source afterFold).2.clock≤6 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outputArguments=some (CopyGeneral.values out acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,outputArguments,localVar,accumulator,output,CopyGeneral.values]
  have copyCost := CopyGeneral.call_cost_arena source outputArguments acc out 32 args (CopyGeneral.original_code source.code workspace.installed) workspace.domain accArena outArena
  have blocks := CopyGeneral.cost_word_multiple acc out 32 (by decide)
  have tailPrice : ClockCost.Bound source.code (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))) 1 :=
    ClockCost.sequence source.code _ _ 1 0 (HeapScope.release_call_cost source.code workspace.installed (some none) _) (ClockCost.returned source.code _)
  rw [fold_shape.2.2.2.2.2]
  exact ClockCost.sequence_current source _ _ 5 1 (by omega) tailPrice

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots acc out stp accel : BitVec 64) (k : Nat)
    (inside : k≤15) (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source afterZeroAcc).2.clock≤54*k+6 := by
  have foldCost := fold_loop_cost source roots acc stp accel k inside workspace root accumulator round rootsArena accArena
  rw [fold_shape.2.2.2.2.1]
  apply ClockCost.sequence_reached_current source foldLoop afterFold (54*k) 6 foldCost
  intro middle normal
  have nextWorkspace := ShaPair.Workspace.after source middle stp accel workspace foldLoop none normal
    (fold_loop_globals (ofString "sha_st") source.code workspace.installed) (fold_loop_globals (ofString "sha_accel") source.code workspace.installed)
  have other (name : String) (different : ofString name≠ofString "k") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (fold_loop_other (ofString name) different).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact output_cost middle acc out nextWorkspace ((other "acc" (by decide)).trans accumulator) ((other "out" (by decide)).trans output) accArena outArena

/-- Complete original zero/fold/output/release suffix costs54 per actual
saved root plus8, at most818 for all real progressive exits. -/
theorem suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots acc out stp accel : BitVec 64) (k : Nat)
    (inside : k≤15) (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) (aligned : acc.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterLoop).2.clock≤54*k+8 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,accumulator,Zero.values]
  have zeroCost := Zero.call_cost source zeroArguments acc 32 args (Zero.original_code source.code workspace.installed) (by decide) (by decide) aligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source acc 32 index workspace.domain accArena (by omega) aligned multiple)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") zeroArguments)).2.clock≤2 at zeroCost
  rw [fold_shape.2.2.2.1]
  have cost := ClockCost.sequence_reached_current source _ afterZeroAcc 2 (54*k+6) zeroCost (by
    intro middle normal
    have zeroGlobals (key : MlS) : GlobalEffects.Preserves key source.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
      GlobalEffects.call_body key source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
        (Zero.original_code source.code workspace.installed) (Zero.globals key source.code)
    have nextWorkspace := ShaPair.Workspace.after source middle stp accel workspace _ none normal (zeroGlobals (ofString "sha_st")) (zeroGlobals (ofString "sha_accel"))
    have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
      have safe : LocalPrefix (ofString name) (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro key impossible; cases impossible)
      have summary := safe.summary_full source
      unfold LocalSummary at summary
      rw [normal] at summary
      exact summary.1 rfl
    exact after_zero_cost middle roots acc out stp accel k inside nextWorkspace ((other "roots").trans root) ((other "acc").trans accumulator) ((other "out").trans output) ((other "k").trans round) rootsArena accArena outArena)
  omega

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.fold_loop_globals
#print axioms InitECandidate.Solver.Input.Progressive.fold_loop_other
#print axioms InitECandidate.Solver.Input.Progressive.output_cost
#print axioms InitECandidate.Solver.Input.Progressive.after_zero_cost
#print axioms InitECandidate.Solver.Input.Progressive.suffix_cost

import InitECandidate.Solver.Input.PContainerBitLoop
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp act out stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (tmpArena : AllocatedBytes.Arena tmp 32) (actArena : AllocatedBytes.Arena act 32) :
    source.clock-(evaluateHOLFiniteState source afterLoop).2.clock≤54 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) shaArguments=some (ShaPair.values tmp act out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,shaArguments,localVar,temporary,activity,output,ShaPair.values]
  have price := ShaPair.call_cost source tmp act out stp accel workspace.installed (some none) shaArguments args
    workspace.state workspace.accelerator workspace.domain tmpArena actArena workspace.arena workspace.aligned
  have releaseCost : ClockCost.Bound source.code afterSha 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code workspace.installed (some none) _) (ClockCost.returned source.code _)
  rw [body_shape.2.2.2.2.2.2.2.2.2]
  exact ClockCost.sequence_current source _ _ 53 1 price releaseCost

theorem loop_suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp act out stp accel : BitVec 64) (n : Nat)
    (short : n<32) (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (tmpArena : AllocatedBytes.Arena tmp 32) (actArena : AllocatedBytes.Arena act 32) :
    source.clock-(evaluateHOLFiniteState source loopAndSuffix).2.clock≤n+54 := by
  have loopPrice := bit_loop_cost source n 0 short (by omega) position count
  rw [body_shape.2.2.2.2.2.2.1]
  apply ClockCost.sequence_reached_current source bitLoop afterLoop n 54 (by simpa using loopPrice)
  intro middle normal
  have nextWorkspace := ShaPair.Workspace.after source middle stp accel workspace bitLoop none normal
    (bit_loop_globals (ofString "sha_st") source.code) (bit_loop_globals (ofString "sha_accel") source.code)
  have other (name : String) (different : ofString name≠ofString "i") : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary : LocalSummary (ofString name) bitLoop source := by
      rw [body_shape.2.2.2.2.2.2.2.1]
      exact while_local_summary (ofString name) test bitStep (bit_step_summary (ofString name) different) source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact after_loop_cost middle tmp act out stp accel nextWorkspace ((other "tmp" (by decide)).trans temporary)
    ((other "act" (by decide)).trans activity) ((other "out" (by decide)).trans output) tmpArena actArena

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp act out stp accel : BitVec 64) (n : Nat)
    (short : n<32) (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (tmpArena : AllocatedBytes.Arena tmp 32) (actArena : AllocatedBytes.Arena act 32) :
    source.clock-(evaluateHOLFiniteState source afterZero).2.clock≤n+54 := by
  let entry := bind source "i" 0#64
  have nextWorkspace := ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl
  have other (name : String) (different : ofString "i"≠ofString name) := bind_lookup_other source "i" name 0#64 different
  have price := loop_suffix_cost entry tmp act out stp accel n short nextWorkspace
    ((other "tmp" (by decide)).trans temporary) ((other "act" (by decide)).trans activity) ((other "out" (by decide)).trans output)
    ((other "n" (by decide)).trans count) (bind_lookup_same _ _ _) tmpArena actArena
  rw [body_shape.2.2.2.2.2.1]
  exact ClockCost.declared_current source "i" (.const 0#64) 0#64 loopAndSuffix (n+54) rfl price

/-- Actual activity-mask zeroing, bounded bit loop and final SHA/release
suffix. No activity bytes or future successful helper result is assumed. -/
theorem after_act_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp act out stp accel : BitVec 64) (n : Nat)
    (short : n<32) (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (tmpArena : AllocatedBytes.Arena tmp 32) (actArena : AllocatedBytes.Arena act 32) (aligned : act.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterAct).2.clock≤n+56 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values act 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,activity,Zero.values]
  have zeroCost := Zero.call_cost source zeroArguments act 32 args (Zero.original_code source.code workspace.installed) (by decide) (by decide) aligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source act 32 index workspace.domain actArena (by omega) aligned multiple)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") zeroArguments)).2.clock≤2 at zeroCost
  rw [body_shape.2.2.2.2.1]
  have price := ClockCost.sequence_reached_current source _ afterZero 2 (n+54) zeroCost (by
    intro middle normal
    have zeroGlobals (key : MlS) : GlobalEffects.Preserves key source.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
      GlobalEffects.call_body key source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
        (Zero.original_code source.code workspace.installed) (Zero.globals key source.code)
    have nextWorkspace := ShaPair.Workspace.after source middle stp accel workspace _ none normal (zeroGlobals (ofString "sha_st")) (zeroGlobals (ofString "sha_accel"))
    have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source middle (ofString name) (ofString "memzero") zeroArguments normal
    exact after_zero_cost middle tmp act out stp accel n short nextWorkspace ((other "tmp").trans temporary)
      ((other "act").trans activity) ((other "out").trans output) ((other "n").trans count) tmpArena actArena)
  omega

theorem after_progressive_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp out stp accel : BitVec 64) (n : Nat)
    (short : n<32) (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (arena : AllocatedBytes.Arena tmp 64) (aligned : tmp.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterProgressive).2.clock≤n+56 := by
  let act := tmp+32#64
  let entry := bind source "act" act
  have actArena : AllocatedBytes.Arena act 32 := AllocatedBytes.Arena.subrange tmp 64 32 32 arena (by omega)
  have actNumber : act.toNat=tmp.toNat+32 := BitVec.toNat_add_of_lt (by change tmp.toNat+32<2^64; have upper:=arena.upper; omega)
  have nextWorkspace := ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl
  have other (name : String) (different : ofString "act"≠ofString name) := bind_lookup_other source "act" name act different
  have price := after_act_cost entry tmp act out stp accel n short nextWorkspace ((other "tmp" (by decide)).trans temporary)
    (bind_lookup_same _ _ _) ((other "out" (by decide)).trans output) ((other "n" (by decide)).trans count)
    (AllocatedBytes.Arena.weaken tmp 64 32 arena (by omega)) actArena (by rw [actNumber]; omega)
  have read : eval source (.op .add [localVar "tmp",.const 32#64])=some (.val (.word act)) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,temporary,valueIsWord,valueWord,wordOpHOL,wordOp,act]
  rw [body_shape.2.2.2.1]
  exact ClockCost.declared_current source "act" _ act afterAct (n+56) read price

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_loop_cost
#print axioms InitECandidate.Solver.Input.PContainer.loop_suffix_cost
#print axioms InitECandidate.Solver.Input.PContainer.after_zero_cost
#print axioms InitECandidate.Solver.Input.PContainer.after_act_cost
#print axioms InitECandidate.Solver.Input.PContainer.after_progressive_cost

import InitECandidate.Solver.Input.MerkleOuterProgram

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real half/j declarations and inner pair loop fit54*floor(cur/2)
source ticks. Signed-comparison bounds come from the actual buffer arena. -/
theorem outer_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel : BitVec 64) (cur capacity : Nat)
    (inside : cur≤capacity) (arena : AllocatedBytes.Arena cursor (32*capacity)) (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) :
    source.clock-(evaluateHOLFiniteState source outerStep).2.clock≤54*(cur/2) := by
  have upper := arena.upper
  have small : cur<2^64 := by omega
  have halfSmall : cur/2<2^63 := by omega
  have innerArena : AllocatedBytes.Arena cursor (64*(cur/2)) := AllocatedBytes.Arena.weaken cursor (32*capacity) (64*(cur/2)) arena (by omega)
  have entryWorkspace := ShaPair.Workspace.of_fields source (innerEntry source cur) stp accel workspace rfl rfl rfl rfl
  have entryBuffer : (innerEntry source cur).locals.lookup (ofString "buf")=some (.val (.word cursor)) :=
    (bind_lookup_other _ "j" "buf" _ (by decide)).trans ((bind_lookup_other source "half" "buf" _ (by decide)).trans buffer)
  have entryHalf : (innerEntry source cur).locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have entryJ : (innerEntry source cur).locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 0))) := bind_lookup_same _ _ _
  have innerCost := inner_loop_cost (innerEntry source cur) cursor stp accel 0 (cur/2) halfSmall (by omega) innerArena entryWorkspace entryJ entryHalf entryBuffer
  rw [outer_shape.2.1]
  apply ClockCost.declared_current source "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf (54*(cur/2)) (half_read source cur small current)
  change (halfEntry source cur).clock-(evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) outerInnerTail)).2.clock≤_
  apply ClockCost.declared_current (halfEntry source cur) "j" (.const 0#64) 0#64 outerInnerTail (54*(cur/2)) rfl
  exact ClockCost.sequence_current (innerEntry source cur) innerLoop outerAssign (54*(cur/2)) 0 (by simpa only [Nat.sub_zero] using innerCost)
    (ClockCost.assign (innerEntry source cur).code _ _)

/-- The dense allowance pays for the actual inner pairs, one outer tick,
and the smaller next-cur allowance. It telescopes across all halving rounds. -/
theorem halving_budget (cur : Nat) (active : 1<cur) :
    54*(cur/2)+1+55*(cur/2-1)≤55*(cur-1) := by omega

theorem outer_workspace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel) (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source outerStep=(result,post)) :
    ShaPair.Workspace post stp accel :=
  ShaPair.Workspace.after source post stp accel workspace outerStep result run
    (outer_globals (ofString "sha_st") source.code workspace.installed) (outer_globals (ofString "sha_accel") source.code workspace.installed)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.outer_step_cost
#print axioms InitECandidate.Solver.Input.Merkle.halving_budget
#print axioms InitECandidate.Solver.Input.Merkle.outer_workspace

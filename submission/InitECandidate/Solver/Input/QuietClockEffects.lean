import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Input.QuietClock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Either local/global assignment spends no source call/loop clock. -/
theorem assign_kind (code) (kind : VarKind) (name : MlS) (expression : ExpHOL 64) :
    Preserves code (.assign kind name expression) := by
  intro source installed
  cases kind <;> rw [evaluateHOLFiniteState_assign]
  all_goals repeat first | rfl | split

/-- These atomic source effects may alter FFI/memory but do not spend a
source call/loop clock. Their target work remains a separate obligation. -/
theorem shared_store (code) (size : OpSize) (address expression : ExpHOL 64) :
    Preserves code (.shMemStore size address expression) := by
  intro source installed
  classical
  rw [evaluateHOLFiniteState_shMemStore]
  change (shMemStoreClauseHOLFiniteExact source size address expression).2.clock=source.clock
  unfold shMemStoreClauseHOLFiniteExact
  exact shMemStoreClauseHOLExact_clock _ _ _ _ _

theorem external (code) (name : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    Preserves code (.extCall name configuration configurationLength array arrayLength) := by
  intro source installed
  rw [evaluateHOLFiniteState_extCall_source]
  repeat first | rfl | split

end InitECandidate.Solver.Input.QuietClock

#print axioms InitECandidate.Solver.Input.QuietClock.assign_kind
#print axioms InitECandidate.Solver.Input.QuietClock.shared_store
#print axioms InitECandidate.Solver.Input.QuietClock.external

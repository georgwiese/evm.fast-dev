import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Input.QuietClock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem shared_store (code) (size : OpSize) (address value : ExpHOL 64) : Preserves code (.shMemStore size address value) := by
  intro source installed
  classical
  rw [evaluateHOLFiniteState_shMemStore]
  change (shMemStoreClauseHOLFiniteExact source size address value).2.clock=source.clock
  exact @shMemStoreClauseHOLExact_clock 64 Guest.HostMemory _ source.toExact
    (fun query=>Classical.propDecidable (source.shMemaddrs query)) size address value
    (fun _ expression=>@evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) expression)

theorem assign_global (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .global name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split <;> rfl

/-- A zero-tick suffix keeps the real first phase's final clock on every
outcome, independently of the first phase's effects or own runtime. -/
theorem sequence_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (quiet : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState current second).2.clock=current.clock) :
    (evaluateHOLFiniteState source (.seq first second)).2.clock=(evaluateHOLFiniteState source first).2.clock := by
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output
  obtain ⟨result,middle⟩ := output
  cases result with
  | none=>exact quiet middle
  | some result=>rfl

end InitECandidate.Solver.Input.QuietClock

#print axioms InitECandidate.Solver.Input.QuietClock.shared_store
#print axioms InitECandidate.Solver.Input.QuietClock.assign_global
#print axioms InitECandidate.Solver.Input.QuietClock.sequence_clock

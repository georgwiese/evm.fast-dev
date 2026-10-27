import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.NormalHeapEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat)
    (same : LocalEffects.erase source = LocalEffects.erase target) (initial : AtLeast lower source) : AtLeast lower target := by
  obtain ⟨pointer, cell, low, high, aligned⟩ := initial
  have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup (ofString "heap_ptr")) same
  exact ⟨pointer, projected.symm.trans cell, low, high, aligned⟩

/-- A real completed lexical trace retains a proven current lower frontier.
The skip sink is evaluated only as evidence for the genuine reached actions;
its lexical restoration does not replace the live continuation state. -/
theorem execution {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List CallPrefix.Action}
    (actual : CallPrefix.Execution source actions target)
    (pure : Preserves source.code (CallPrefix.program actions .skip))
    (lower : Nat) (initial : AtLeast lower source) : AtLeast lower target := by
  have projected := congrArg Prod.fst (actual.project .skip)
  have normal : (evaluateHOLFiniteState source (CallPrefix.program actions .skip)).1 = none := by
    simpa only [CallPrefix.project, evaluateHOLFiniteState_skip] using projected
  have heap := pure source rfl lower initial (by rw [normal]; trivial)
  exact of_erase _ _ lower actual.skip_erase heap

end InitECandidate.Solver.Input.NormalHeapEffects

#print axioms InitECandidate.Solver.Input.NormalHeapEffects.of_erase
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.execution

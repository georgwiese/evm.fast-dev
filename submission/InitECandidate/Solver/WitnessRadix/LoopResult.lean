import InitECandidate.Solver.WitnessRadix.LoopCompose
import InitECandidate.Solver.WitnessRadix.AgendaWeightSteps

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def LoopResult {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (expected : Graph.Tree) (weight : Nat) : Prop :=
  ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
    evaluateHOLFiniteState source BuildEntry.mainLoop = (some (.returned (.val (.word 0#64))), target) ∧
    target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word root ∧
    QueryMemory.Represents target layout.table layout.keys layout.vals root expected ∧
    control target = control source ∧ source.clock - 4 * weight ≤ target.clock ∧ target.clock ≤ source.clock

/-- Compose one checked outer transition with the remaining execution and
its decreasing potential; source clocks and preserved control fields stay explicit. -/
theorem result_next {F : Type} (source next : PanSemStateFiniteExact 64 F) (layout : Layout) (expected : Graph.Tree)
    (weight nextWeight cost : Nat)
    (run : evaluateHOLFiniteState source BuildEntry.mainLoop = evaluateHOLFiniteState next BuildEntry.mainLoop)
    (fields : control next = control source) (clock : next.clock = source.clock - cost)
    (price : cost + 4 * nextWeight ≤ 4 * weight)
    (remaining : LoopResult next layout expected nextWeight) : LoopResult source layout expected weight := by
  obtain ⟨target, root, execution, mapped, word, represented, controls, lower, upper⟩ := remaining
  refine ⟨target, root, run.trans execution, mapped, word, represented, controls.trans fields, ?_, ?_⟩
  · rw [clock] at lower
    omega
  · rw [clock] at upper
    omega

theorem last_exists (input : List (BitVec 64)) (present : input ≠ []) : ∃ ordinal, input.getLast? = some ordinal := by
  cases last : input.getLast? with
  | none => exact False.elim (present (List.getLast?_eq_none_iff.mp last))
  | some ordinal => exact ⟨ordinal, rfl⟩

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.result_next

import InitECandidate.Solver.WitnessRadix.LoopTermination
import InitECandidate.Solver.WitnessRadix.InvariantInitial

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem core_nonempty {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (expected : Graph.Tree)
    (weight : Nat) (count : BitVec 64) (nonzero : count ≠ 0#64)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word count)))
    (loop : LoopResult source layout expected weight) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
      evaluateHOLFiniteState source BuildEntry.core = (some (.returned (.val (.word 0#64))), target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root expected ∧
      control target = control source ∧ source.clock - 4 * weight ≤ target.clock ∧ target.clock ≤ source.clock := by
  classical
  obtain ⟨target, root, run, mapped, word, represented, controls, lower, upper⟩ := loop
  have skipped : evaluateHOLFiniteState source
      (.ite (.cmp .equal (QueryBranch.localVar "n") (.const 0#64))
        (.seq (.store (QueryBranch.localVar "dest") (.const 0#64)) BuildEntry.returnZero) .skip) = (none, source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [QueryBranch.localVar, evalHOLExact, toExact, countLocal, nonzero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine ⟨target, root, ?_, mapped, word, represented, controls, lower, upper⟩
  rw [BuildEntry.core_shape, StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
  exact StateSteps.stopped_sequence source target _ _ _ run upper

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.core_nonempty

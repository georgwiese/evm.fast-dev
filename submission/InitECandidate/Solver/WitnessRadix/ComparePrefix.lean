import InitECandidate.Solver.WitnessRadix.CompareChain

namespace InitECandidate.Solver.WitnessRadix.CompareChain
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def prefixChecks : List Comparison → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | check :: rest, continuation =>
      .seq (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip)
        (prefixChecks rest continuation)

/-- The exact common prefix of the fixed memeq byte-loop body. Every matched
test falls through unchanged, and the first mismatch returns immediately. -/
theorem execute_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (checks : List Comparison) (continuation : ProgHOL 64)
    (ready : ∀ check ∈ checks, Ready state check) :
    evaluateHOLFiniteState state (prefixChecks checks continuation) =
      if agrees checks then evaluateHOLFiniteState state continuation
      else (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite state) := by
  classical
  induction checks with
  | nil => simp [prefixChecks, agrees]
  | cons check rest ih =>
      obtain ⟨left, right⟩ := ready check (by simp)
      simp only [QueryBranch.eval] at left right
      have tail := ih (fun next member => ready next (List.mem_cons_of_mem check member))
      by_cases same : check.first = check.second
      · have skipped : evaluateHOLFiniteState state
          (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip) = (none, state) := by
          rw [evaluateHOLFiniteState_ite]
          simp [evalHOLExact, left, right, same, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [prefixChecks, evaluateHOLFiniteState_seq, skipped]
        have fixed : fixClockHOLFinite state ((none : Option (PanSemResultExact 64)), state) =
            (none, state) := by simp [fixClockHOLFinite]
        simpa [fixed, agrees, same] using tail
      · have stopped : evaluateHOLFiniteState state
          (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip) =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite state) := by
          rw [evaluateHOLFiniteState_ite]
          simpa [evalHOLExact, left, right, same, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            using return_word state 0#64
        rw [prefixChecks, evaluateHOLFiniteState_seq, stopped]
        simp [fixClockHOLFinite, emptyLocalsHOLFinite, agrees, same]

end InitECandidate.Solver.WitnessRadix.CompareChain

#print axioms InitECandidate.Solver.WitnessRadix.CompareChain.execute_prefix

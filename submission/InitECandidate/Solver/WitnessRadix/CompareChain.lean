import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.WitnessRadix.CompareChain
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

structure Comparison where
  left : ExpHOL 64
  right : ExpHOL 64
  first : BitVec 64
  second : BitVec 64

def returned (word : BitVec 64) : ProgHOL 64 := .return (.const word)

def chain : List Comparison → ProgHOL 64
  | [] => returned 1#64
  | check :: rest =>
      .seq (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip) (chain rest)

def Ready {F : Type} (state : PanSemStateFiniteExact 64 F) (check : Comparison) : Prop :=
  QueryBranch.eval state check.left = some (.val (.word check.first)) ∧
  QueryBranch.eval state check.right = some (.val (.word check.second))

def agrees (checks : List Comparison) : Bool := checks.all fun check => check.first == check.second

theorem return_word {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64) :
    evaluateHOLFiniteState state (returned word) =
      (some (.returned (.val (.word word))), emptyLocalsHOLFinite state) := by
  simp [returned, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
    sizeOfShapeWithContextHOL]

/-- A sequence of early-mismatch comparisons has no clock cost of its own.
The real memory-load premises are supplied by the caller. -/
theorem execute {F : Type} (state : PanSemStateFiniteExact 64 F) (checks : List Comparison)
    (ready : ∀ check ∈ checks, Ready state check) :
    evaluateHOLFiniteState state (chain checks) =
      (some (.returned (.val (.word (if agrees checks then 1#64 else 0#64)))),
        emptyLocalsHOLFinite state) := by
  classical
  induction checks with
  | nil => simpa [chain, agrees] using return_word state 1#64
  | cons check rest ih =>
      obtain ⟨left, right⟩ := ready check (by simp)
      simp only [QueryBranch.eval] at left right
      have tail := ih (fun next member => ready next (List.mem_cons_of_mem check member))
      by_cases same : check.first = check.second
      · have skipped : evaluateHOLFiniteState state
          (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip) = (none, state) := by
          rw [evaluateHOLFiniteState_ite]
          simp [evalHOLExact, left, right, same, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [chain, evaluateHOLFiniteState_seq, skipped]
        have fixed : fixClockHOLFinite state ((none : Option (PanSemResultExact 64)), state) =
            (none, state) := by simp [fixClockHOLFinite]
        simpa [fixed, agrees, same] using tail
      · have stopped : evaluateHOLFiniteState state
          (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip) =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite state) := by
          rw [evaluateHOLFiniteState_ite]
          simpa [evalHOLExact, left, right, same, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            using return_word state 0#64
        rw [chain, evaluateHOLFiniteState_seq, stopped]
        simp [fixClockHOLFinite, emptyLocalsHOLFinite, agrees, same]

end InitECandidate.Solver.WitnessRadix.CompareChain

#print axioms InitECandidate.Solver.WitnessRadix.CompareChain.execute

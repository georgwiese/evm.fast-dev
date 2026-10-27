import InitECandidate.Solver.Input.ScalarDeclaration
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A real fall-through sequence ran both pieces to fall-through. -/
theorem sequence_none {F : Type} (source post : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (run : evaluateHOLFiniteState source (.seq first second) = (none, post)) :
    ∃ middle, evaluateHOLFiniteState source first = (none, middle) ∧ evaluateHOLFiniteState middle second = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source first = output at run ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact ⟨middle, rfl, run⟩
  | some result => cases run

theorem declaration_none {F : Type} (source post : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64)
    (read : eval source expression = some (.val (.word word)))
    (run : evaluateHOLFiniteState source (.dec (Flapjack.Basis.Pure.MlString.ofString name) .one expression body) = (none, post)) :
    ∃ inner, evaluateHOLFiniteState (bind source name word) body = (none, inner) ∧ post = restore source name inner := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have actual := ScalarScope.declare_execute source output.2 name expression word body output.1 read rfl
  rw [actual] at run
  have resultEq := congrArg Prod.fst run
  have postEq := congrArg Prod.snd run
  exact ⟨output.2, Prod.ext resultEq rfl, postEq.symm⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_none
#print axioms InitECandidate.Solver.Input.declaration_none

import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.ScalarWordShape

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual successful assignment to a current scalar binding derives the
new scalar read and complete update, without assuming expression success. -/
theorem scalar_assign_none {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (old : BitVec 64)
    (present : source.locals.lookup (ofString name) = some (.val (.word old)))
    (normal : evaluateHOLFiniteState source (.assign .local (ofString name) expression) = (none, post)) :
    ∃ word : BitVec 64, eval source expression = some (.val (.word word)) ∧ post = bind source name word := by
  classical
  rw [evaluateHOLFiniteState_assign] at normal
  cases read : evalHOLExact source.toExact expression with
  | none => simp only [read] at normal; cases normal
  | some value =>
    simp only [read] at normal
    split at normal
    · rename_i valid
      have typed : shapeOfHOLExact value = .one := by
        apply (shapeEqHOL_eq_true _ _).mp
        simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, present, shapeOfHOLExact] using valid
      obtain ⟨word, valueEq⟩ := scalar_word_of_shape value typed
      subst value
      have postEq := congrArg Prod.snd normal
      exact ⟨word, read, postEq.symm⟩
    · cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.scalar_assign_none

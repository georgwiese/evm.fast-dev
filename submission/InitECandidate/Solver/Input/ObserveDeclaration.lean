import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A known scalar declaration exposes the same actual inner outcome, with
only its lexical binding restored at the parent endpoint. -/
theorem declaration_observe {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (read : eval source expression = some (.val (.word word)))
    (actual : evaluateHOLFiniteState source (.dec (ofString name) .one expression body) = (result, post)) :
    ∃ inner, evaluateHOLFiniteState (bind source name word) body = (result, inner) ∧ post = restore source name inner := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have declared := declare_execute source output.2 name expression word body output.1 read rfl
  rw [declared] at actual
  have observed : output.1 = result := congrArg Prod.fst actual
  exact ⟨output.2, Prod.ext observed rfl, (congrArg Prod.snd actual).symm⟩

end InitECandidate.Solver.Input.ScalarScope

#print axioms InitECandidate.Solver.Input.ScalarScope.declaration_observe

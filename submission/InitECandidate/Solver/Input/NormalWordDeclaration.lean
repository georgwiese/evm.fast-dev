import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem declaration_return_word {F : Type} (source post : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (returned : ValueHOL 64)
    (read : eval source expression = some (.val (.word word)))
    (run : evaluateHOLFiniteState source (.dec (Flapjack.Basis.Pure.MlString.ofString name) .one expression body) = (some (.returned returned), post)) :
    ∃ inner, evaluateHOLFiniteState (bind source name word) body = (some (.returned returned), inner) ∧ post = restore source name inner := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have actual := ScalarScope.declare_execute source output.2 name expression word body output.1 read rfl
  rw [actual] at run
  have resultEq := congrArg Prod.fst run
  have postEq := congrArg Prod.snd run
  exact ⟨output.2, Prod.ext resultEq rfl, postEq.symm⟩

/-- Invert a real scalar declaration whose continuation falls through. -/
theorem declaration_none_word {F : Type} (source post : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64)
    (read : eval source expression=some (.val (.word word)))
    (run : evaluateHOLFiniteState source (.dec (Flapjack.Basis.Pure.MlString.ofString name) .one expression body)=(none,post)) :
    ∃ inner,evaluateHOLFiniteState (bind source name word) body=(none,inner) ∧ post=restore source name inner := by
  let output:=evaluateHOLFiniteState (bind source name word) body
  have actual:=ScalarScope.declare_execute source output.2 name expression word body output.1 read rfl
  rw [actual] at run
  have resultEq:=congrArg Prod.fst run
  have postEq:=congrArg Prod.snd run
  exact ⟨output.2,Prod.ext resultEq rfl,postEq.symm⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.declaration_return_word

#print axioms InitECandidate.Solver.Input.declaration_none_word

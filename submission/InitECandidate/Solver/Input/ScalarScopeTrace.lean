import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A known actual scalar read exposes its real continuation and lexical
restoration on every outcome, including exceptions. -/
theorem declare_trace {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (read : eval source expression=some (.val (.word word)))
    (run : evaluateHOLFiniteState source (.dec (Flapjack.Basis.Pure.MlString.ofString name) .one expression body)=(result,target)) :
    ∃ inner,evaluateHOLFiniteState (bind source name word) body=(result,inner) ∧ target=restore source name inner := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have actual := declare_execute source output.2 name expression word body output.1 read rfl
  rw [actual] at run
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  exact ⟨output.2,Prod.ext observed rfl,endpoint.symm⟩

end InitECandidate.Solver.Input.ScalarScope
#print axioms InitECandidate.Solver.Input.ScalarScope.declare_trace

import InitECandidate.Solver.PanDeclarations

/-! Scalar scope execution, independent of allocation, input buffers and hashing. -/
namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual scalar declaration and lexical restoration for any host state. -/
theorem declare_execute {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (read : eval source expression = some (.val (.word word)))
    (run : evaluateHOLFiniteState (bind source name word) body = (result, target)) :
    evaluateHOLFiniteState source (.dec (ofString name) .one expression body) =
      (result, restore source name target) := by
  have setup : WitnessRadix.BuildEntry.Initializes source [(name, expression)] (bind source name word)
      (fun post => restore source name post) :=
    .step word read (.done _)
  have actual := WitnessRadix.BuildEntry.declarations_execute setup body
  change evaluateHOLFiniteState source (.dec (ofString name) .one expression body) = _ at actual
  rw [run] at actual
  exact actual

end InitECandidate.Solver.Input.ScalarScope

#print axioms InitECandidate.Solver.Input.ScalarScope.declare_execute

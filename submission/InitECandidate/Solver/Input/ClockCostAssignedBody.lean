import InitECandidate.Solver.Input.ClockCostAssignedCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Uniform body bounds also cover global result destinations and failed
dynamic argument evaluation or lookup. -/
theorem assigned_body (code) (destination : Option (VarKind×MlS)) (function : MlS)
    (arguments : List (ExpHOL 64)) (formals : List (MlS×ShapeHOL)) (body : ProgHOL 64)
    (returnShape : ShapeHOL) (price : Nat) (entry : code.lookup function=some (formals,body,returnShape))
    (priced : Bound code body price) : Bound code (.call (some (destination,none)) function arguments) (price+1):=by
  intro source codeEq
  cases args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments with
  | none=>rw [evaluateHOLFiniteState_call,args]; simp only; omega
  | some values=>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp only; omega
    | some data=>
      obtain ⟨actual,callee,shape⟩:=data
      have currentEntry : source.code.lookup function=some (formals,body,returnShape):=by rw [codeEq]; exact entry
      have same:=LocalEffects.lookup_body source.code function formals body returnShape currentEntry values actual callee shape called
      subst actual
      exact assigned_current source destination function arguments values body callee shape price args called
        (priced (callEntryStateHOLFinite source callee) codeEq)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.assigned_body

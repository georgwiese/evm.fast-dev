import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real scalar declaration preserves the result and clock of its same
continuation. Non-timeout is derived from the enclosing observation. -/
theorem declared_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (price : Nat)
    (read : eval source expression=some (.val (.word word)))
    (tail : ∀ result target,evaluateHOLFiniteState (bind source name word) body=(result,target) → result≠some .timeOut → source.clock-target.clock≤price)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (.dec (ofString name) .one expression body)=(result,post))
    (notTimeout : result≠some .timeOut) : source.clock-post.clock≤price := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have executed := ScalarScope.declare_execute source output.2 name expression word body output.1 read rfl
  have resultEq : result=output.1 := congrArg Prod.fst (actual.symm.trans executed)
  have clockEq := congrArg (fun output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>output.2.clock) (actual.symm.trans executed)
  change post.clock=output.2.clock at clockEq
  have observed : output.1≠some .timeOut := by rw [←resultEq]; exact notTimeout
  have paid := tail output.1 output.2 rfl observed
  rw [clockEq]
  exact paid

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.declared_terminating

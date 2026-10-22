import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Invert a genuine declaration action using its independently derived
current read. The next caller state is the real local update. -/
theorem Reaches.declare_target {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {shape : ShapeHOL} {expression : ExpHOL 64} (value : ValueHOL 64)
    (reached : Reaches source (.declare name shape expression) target)
    (read : WitnessRadix.QueryBranch.eval source expression=some value) : target=setVarHOLFinite name value source := by
  cases reached with
  | declare _ _ _ actual actualRead checked=>
    have same : actual=value:=Option.some.inj (actualRead.symm.trans read)
    rw [same]

theorem Execution.declare_next {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {shape : ShapeHOL} {expression : ExpHOL 64} {rest : List Action} (value : ValueHOL 64)
    (execution : Execution source (.declare name shape expression::rest) target)
    (read : WitnessRadix.QueryBranch.eval source expression=some value) :
    Execution (setVarHOLFinite name value source) rest target := by
  cases execution with
  | step first next=>
    have same:=first.declare_target value read
    cases same
    exact next

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.declare_target
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.declare_next

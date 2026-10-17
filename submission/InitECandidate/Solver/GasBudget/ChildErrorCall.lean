import InitECandidate.Solver.GasBudget.ChildError

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word child)])
    (code : source.code.lookup (ofString "incorporate_child_on_error")=some (formals,body,.one))
    (ready : Ready source parent child p c)
    (gasFits : p.gas.toNat+c.gas.toNat<2^64) (usedFits : p.used.toNat+c.used.toNat<2^64) (enough : 1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "incorporate_child_on_error") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-1}) ∧
      regularBudget memory parent+(wordAt source.memory (child+192#64)).toNat=
        regularBudget source.memory parent+regularBudget source.memory child := by
  obtain ⟨callee,called,childLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "incorporate_child_on_error") "child" body child code
  let entry:=callEntryStateHOLFinite source callee
  let memory:=WitnessRadix.WordWrites.write source.memory (writes parent p c)
  have enteredReady : Ready entry parent child p c:=
    ⟨ready.ev,childLocal,ready.parentMapped,ready.childMapped,ready.parentCells,ready.childCells,ready.separate⟩
  have run:=execute entry parent child p c enteredReady
  have frameEq : emptyLocalsHOLFinite (emptyLocalsHOLFinite {entry with memory:=memory})=
      emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1}:=rfl
  exact ⟨memory,ignored_return source _ _ expressions _ body callee 1 args called enough run frameEq,
    budget_transfer source parent child p c ready gasFits usedFits⟩

theorem returned_budget_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (ready : Ready source parent child p c)
    (gasFits : p.gas.toNat+c.gas.toNat<2^64) (usedFits : p.used.toNat+c.used.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (writes parent p c)) parent≤
      regularBudget source.memory parent+regularBudget source.memory child := by
  have transfer:=budget_transfer source parent child p c ready gasFits usedFits
  omega

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.call_execute
#print axioms InitECandidate.Solver.GasBudget.ChildError.returned_budget_bound

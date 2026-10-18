import InitECandidate.Solver.GasBudget.ChildErrorNormalCall

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original child-error incorporation derives its call clock and
complete three-store memory result. The source amounts may wrap here;
physical live-budget bounds supply natural non-wrap in the sum theorem. -/
theorem call_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word child)])
    (code : source.code.lookup (ofString "incorporate_child_on_error") = some (formals, body, .one))
    (ready : Ready source parent child p c)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "incorporate_child_on_error") expressions) = (none, target)) :
    1 ≤ source.clock ∧ target = {source with memory := WitnessRadix.WordWrites.write source.memory (writes parent p c), clock := source.clock - 1} := by
  obtain ⟨callee, called, childLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "incorporate_child_on_error") "child" body child code
  obtain ⟨positive, post, returned, actualRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "incorporate_child_on_error") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have incoming : Ready entry parent child p c :=
    ⟨ready.ev, childLocal, ready.parentMapped, ready.childMapped, ready.parentCells, ready.childCells, ready.separate⟩
  have bodyRun := execute entry parent child p c incoming
  let memory := WitnessRadix.WordWrites.write source.memory (writes parent p c)
  let final := emptyLocalsHOLFinite {entry with memory := memory}
  have fields : emptyLocalsHOLFinite final = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - 1} := rfl
  have actual := ignored_return source final (ofString "incorporate_child_on_error") expressions [.val (.word child)] body callee 1 args called positive bodyRun fields
  have same := congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨positive, same⟩

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.call_memory

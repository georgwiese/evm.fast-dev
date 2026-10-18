import InitECandidate.Solver.GasBudget.ChildSuccess
import InitECandidate.Solver.GasBudget.ChildErrorNormalCall
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.GasBudget.ChildSuccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual successful child incorporation reaches the unchanged log/union
suffix with the combined parent/child regular budget. The cap supplies every
arithmetic no-wrap condition and the real first call supplies its clock.
The subsequent log/table work still needs its own ownership and price. -/
theorem body_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64)
    (p c : ChildError.Amounts) (parentSpill childSpill : BitVec 64)
    (ready : Ready source parent child p c parentSpill childSpill)
    (code : source.code.lookup (ofString "incorporate_child_on_error") = some (ChildError.formals, ChildError.body, .one))
    (cap : regularBudget source.memory parent + regularBudget source.memory child ≤ 16777216)
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    1 ≤ source.clock ∧ ∃ entered finish,
      emptyLocalsHOLFinite entered = emptyLocalsHOLFinite {source with memory := entered.memory, clock := source.clock - 1} ∧
      regularBudget entered.memory parent = regularBudget source.memory parent + regularBudget source.memory child ∧
      evaluateHOLFiniteState entered suffix = (some (.returned returned), finish) ∧
      post = restore source "rep" finish := by
  rw [body_shape, program] at normal
  have safe : Input.LocalPrefix (ofString "child") (.call (some (none, none)) (ofString "incorporate_child_on_error") [localVar "child"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨calledPost, firstRun, tailRun, saved⟩ := safe.normal_continue source post
    (.seq (ChildError.sumStore 192#64) (Repayment.program suffix)) returned normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "child"] = some [.val (.word child)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, ready.childLocal]
  have first := ChildError.call_normal source calledPost parent child p c [localVar "child"] args code ready.toReady cap firstRun
  have fits : regularBudget source.memory parent + regularBudget source.memory child < 2 ^ 64 := by omega
  obtain ⟨entered, frame, budget, locals, execute⟩ := execute_prefix source parent child p c parentSpill childSpill ready code fits first.1
  have whole : evaluateHOLFiniteState source (program suffix) = (some (.returned returned), post) := normal
  rw [execute suffix] at whole
  let finish := (evaluateHOLFiniteState entered suffix).2
  have result := congrArg Prod.fst whole
  change (evaluateHOLFiniteState entered suffix).1 = some (.returned returned) at result
  have final := congrArg Prod.snd whole
  exact ⟨first.1, entered, finish, frame, budget, Prod.ext result rfl, final.symm⟩

end InitECandidate.Solver.GasBudget.ChildSuccess

#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.body_normal_prefix

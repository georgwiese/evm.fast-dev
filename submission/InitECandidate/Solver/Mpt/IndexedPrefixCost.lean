import InitECandidate.Solver.Mpt.IndexedSetup
import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.CallPrefixTrace

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem setup_cost (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code (Input.CallPrefix.program actions .skip) 4 := by
  change Input.ClockCost.Bound code (.decCall (ofString "mark") .one (ofString "heap_mark") []
    (.decCall (ofString "m") .one (ofString "mpt_new") [.const 0#64,.const 0#64]
      (.dec (ofString "i") .one (.const 0#64) .skip))) 4
  have markBound : Input.ClockCost.Bound code Input.HeapScope.markBody 0:=by
    rw [Input.HeapScope.mark_shape]
    exact Input.ClockCost.returned code _
  apply Input.ClockCost.scoped_body code _ _ _ _ _ [] Input.HeapScope.markBody .one 0 3
    (Input.OriginalRlp.heap_mark code installed) markBound
  apply Input.ClockCost.scoped_body code _ _ _ _ _ NewTrie.formals NewTrie.body .one 2 0
    (NewTrie.original_code code installed) (NewTrie.body_cost code installed)
  exact Input.ClockCost.declared code _ _ _ _ 0 (Input.ClockCost.skip code)

theorem prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : Input.OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤4 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,Input.CallPrefix.Execution source actions current ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤4 ∧ post.clock=inner.clock ∧ evaluateHOLFiniteState current loopAndAfter=(outcome,inner) := by
  rw [body_shape] at run
  have cost:=setup_cost source.code installed source rfl
  rcases Input.CallPrefix.priced_trace source post actions loopAndAfter 4 cost outcome run with stopped|continued
  · exact Or.inl ⟨stopped.1,by intro value; rw [stopped.2]; exact prefix_never source value⟩
  · exact Or.inr continued

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.setup_cost
#print axioms InitECandidate.Solver.Mpt.Indexed.prefix_trace

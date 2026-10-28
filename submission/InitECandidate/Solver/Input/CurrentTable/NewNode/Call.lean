import InitECandidate.Solver.Input.CurrentTable.NewNode.Context
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual current no-grow node allocation costs one scoped call tick,
changes only next-index metadata and retains the genuine continuation. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64)
    (context : Context source table next cap) (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) expressions = some [.val (.word table)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_node") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 1 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase (New.putField source table 64 (next+1#64)) ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 1 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word next))) continuation = (outcome,inner) ∧
        post = restore source name inner := by
  obtain ⟨callee,called,tableCell⟩ := word_environment source.code.lookup (ofString "htab_new_node")
    (ofString "t") body .one table (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have ready : Context entry table next cap := context.of_frame rfl
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_new_node") expressions _ body continuation callee .one 0
    args called (ready.price tableCell) outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨answer,frame,clock⟩ := ready.returned tableCell value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,endpoint⟩

theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64)
    (context : Context source table next cap) (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) expressions = some [.val (.word table)])
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_node") expressions continuation) = (some (.returned value),post)) :
    ∃ target inner,LocalEffects.erase target = LocalEffects.erase (New.putField source table 64 (next+1#64)) ∧
      target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 1 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word next))) continuation = (some (.returned value),inner) ∧
      post = restore source name inner := by
  rcases scoped_trace source post table next cap context installed name expressions continuation args (some (.returned value)) run with stopped | reached
  · exact (stopped.2 value rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.NewNode

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.scoped_returned

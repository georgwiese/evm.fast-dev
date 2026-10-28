import InitECandidate.Solver.Input.CurrentTable.NewContext
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- An actual current table-constructor call either stops within six ticks
without returning from its enclosing scope, or supplies its genuine empty
Patricia table, next workspace, paid clock and original continuation. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap stp pad : BitVec 64)
    (context : Context source heap cap stp pad) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word 32#64),.val (.word cap)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤6 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target inner,
      Returned source target heap cap stp pad ∧ target.clock≤source.clock ∧ source.clock-target.clock≤6 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word heap))) continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,keyCell,capCell⟩:=word_pair_environment source.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap") body .one 32#64 cap (by decide)
    (original_code source.code context.arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : Context entry heap cap stp pad := context.of_frame rfl
  have price:=current_body_cost entry heap cap keyCell capCell ready.capLower ready.heapCell ready.heapLower ready.heapBound ready.heapAligned ready.arena.domain ready.arena.code
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_new") expressions _ body continuation callee .one 5 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨answer,returned⟩:=ready.returned keyCell capCell value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,returned.reanchor (origin:=source) rfl,forward,cost,continued,endpoint⟩

/-- The same classified interface forces an enclosing return through the
actual successful constructor and its physical table contract. -/
theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap stp pad : BitVec 64)
    (context : Context source heap cap stp pad) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word 32#64),.val (.word cap)])
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") expressions continuation)=(some (.returned value),post)) :
    ∃ target inner,Returned source target heap cap stp pad ∧ target.clock≤source.clock ∧ source.clock-target.clock≤6 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word heap))) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  rcases scoped_trace source post heap cap stp pad context name expressions continuation args (some (.returned value)) run with stopped|reached
  · exact (stopped.2 value rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scoped_returned

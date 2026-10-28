import InitECandidate.Solver.Input.CurrentTable.NewLeaf.NoGrow
import InitECandidate.Solver.Input.ScopedCallClassified
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A real normal leaf run pays its own allocation/copy ticks and returns
the exact fresh slot with the complete physical memory update. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (ready : NewNode.Context source table node cap) (fields : Fields source table cap node pos pointer key)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))) (answer : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.returned answer),post)) :
    answer = .val (.word node) ∧ 3 ≤ source.clock ∧ post.clock = source.clock-3 ∧
      LocalEffects.erase post = LocalEffects.erase (model source table cap node pos pointer value) := by
  let padded := {source with clock := source.clock+3}
  have context : NewNode.Context padded table node cap := ready.of_frame rfl
  have paddedFields : Fields padded table cap node pos pointer key := fields.of_frame rfl
  have actual := body_execute padded table cap node pos pointer value key context paddedFields beforeTable installed tableCell keyCell valueCell
    (by change 3 ≤ source.clock+3; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned answer)) post 3
    ⟨run,by intro impossible; cases impossible⟩
  have returned := congrArg Prod.fst (lifted.symm.trans actual)
  have answerEq : answer = .val (.word node) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using returned
  have endpoint := congrArg Prod.snd (lifted.symm.trans actual)
  dsimp only at endpoint
  have clock := congrArg PanSemStateFiniteExact.clock endpoint
  rw [(returned_frame padded table cap node pos pointer value).2] at clock
  change post.clock+3 = source.clock+3-3 at clock
  have frame := congrArg LocalEffects.erase endpoint
  change LocalEffects.erase post = LocalEffects.erase (model source table cap node pos pointer value) at frame
  exact ⟨answerEq,by omega,by omega,frame⟩

/-- Actual current scoped leaf call: stopped outcomes are charged, while
a reached continuation receives the original constructor's real return. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (ready : NewNode.Context source table node cap) (fields : Fields source table cap node pos pointer key)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_leaf") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 4 ∧ ∀ returned,outcome ≠ some (.returned returned)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase (model source table cap node pos pointer value) ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 4 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word node))) continuation = (outcome,inner) ∧
        post = restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell,valueCell⟩ := word_triple_environment source.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value (by decide) (by decide) (by decide)
    (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have context : NewNode.Context entry table node cap := ready.of_frame rfl
  have entryFields : Fields entry table cap node pos pointer key := fields.of_frame rfl
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_new_leaf") expressions _ body continuation callee .one 3
    args called (price entry table cap node pos pointer value key context entryFields beforeTable installed tableCell keyCell valueCell) outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨answer,paid,clock,frame⟩ := normal entry target table cap node pos pointer value key context entryFields beforeTable installed
      tableCell keyCell valueCell returned bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.normal
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scoped_trace

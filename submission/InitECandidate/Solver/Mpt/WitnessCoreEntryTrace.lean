import InitECandidate.Solver.Mpt.WitnessMaterializePrefixTrace
import InitECandidate.Solver.Mpt.WitnessMptWrapperTrace

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Both genuine original wrappers enter the actual explicit-stack body
at unchanged nonlocal state and three real spent calls. Their exceptional
and normal continuations are accounted for by fixed overhead. -/
theorem core_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤5 ∨ ∃ entry target childResult,
      Input.LocalEffects.erase entry=Input.LocalEffects.erase source ∧ entry.clock=source.clock-3 ∧
      entry.locals.lookup (ofString "db")=some (.val (.word db)) ∧ entry.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      evaluateHOLFiniteState entry WitnessCore.body=(childResult,target) ∧ source.clock-post.clock≤entry.clock-target.clock+6 := by
  rcases child_trace source post db pointer length cursor installed dbCell pCell nCell cursorCell outcome run with stopped|outer
  · exact Or.inl (by omega)
  · obtain ⟨middle,outerTarget,outerResult,pure,clock,dbMiddle,pMiddle,nMiddle,markMiddle,outerRun,outerCost⟩ := outer
    have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [Input.LocalEffects.code_of_erase source middle pure]; exact installed
    rcases WitnessMaterializeMpt.child_trace middle outerTarget db pointer length middleInstalled dbMiddle pMiddle nMiddle outerResult outerRun with stopped|inner
    · exact Or.inl (by omega)
    · obtain ⟨entry,target,childResult,entryPure,entryClock,dbEntry,pEntry,nEntry,childRun,innerCost⟩ := inner
      exact Or.inr ⟨entry,target,childResult,entryPure.trans pure,by omega,dbEntry,pEntry,nEntry,childRun,by omega⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.core_trace

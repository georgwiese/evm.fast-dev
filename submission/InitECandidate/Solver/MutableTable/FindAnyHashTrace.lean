import InitECandidate.Solver.MutableTable.HashAny32Cost
import InitECandidate.Solver.MutableTable.FindPrepared
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.EraseResume
import InitECandidate.Solver.Input.RlpWrite.U256Shape
import InitECandidate.Solver.Input.ScopeClock

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Observe the real32-byte hash on every original find_slot path. A
returned hash resumes the exact canonical caller at its actual word and
one spent call tick, with no query mapping or byte-value premise. -/
theorem any_hash_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word query)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word 32#64)))
    (code : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source hashCall=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ hash inner,
      1≤source.clock ∧ evaluateHOLFiniteState (QueryBranch.bind {source with clock:=source.clock-1} "h" hash) afterHash=(outcome,inner) ∧
      post=QueryBranch.restore source "h" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "key",localVar "klen"]=
      some [.val (.word query),.val (.word 32#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,keyCell,lengthCell]
  obtain ⟨callee,called,pCell,nCell⟩ := Hash.environment source.code.lookup query code
  let entry:=callEntryStateHOLFinite source callee
  have priced:=HashAny32.body_cost entry nCell
  rcases Input.CallNormal.scoped_trace source post "h" .one (ofString "htab_hash") [localVar "key",localVar "klen"] _ Hash.body afterHash callee .one 0
      args called priced outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩ := reached
    have shape : shapeOfHOLExact value=.one := (shapeEqHOL_eq_true _ _).mp (by simpa using checked)
    obtain ⟨hash,valueEq⟩ := Input.RlpWrite.U256Value.scalar_word value shape
    rw [valueEq] at continued
    have pure:=HashAny32.readonly source.code entry rfl
    rw [bodyRun] at pure
    have frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source := pure
    have clockBound:=evaluateHOLFiniteState_clock_le entry Hash.body
    rw [bodyRun] at clockBound priced
    change target.clock≤source.clock-1 at clockBound
    change source.clock-1-target.clock≤0 at priced
    have clock : target.clock=source.clock-1 := by omega
    have same:=Input.CallNormal.continuation_of_erase source target "h" (.val (.word hash)) frame
    rw [clock] at same
    change Input.CallNormal.continuationEntry source target "h" (.val (.word hash))=QueryBranch.bind {source with clock:=source.clock-1} "h" hash at same
    rw [same] at continued
    exact Or.inr ⟨hash,inner,funded,continued,endpoint⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_hash_trace

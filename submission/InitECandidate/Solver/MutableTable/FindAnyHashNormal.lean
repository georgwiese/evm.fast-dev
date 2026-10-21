import InitECandidate.Solver.MutableTable.FindAnyHashTrace

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal hash scope supplies the actual hash word and exact
resumed finder state. No future success or readable query is a premise. -/
theorem any_hash_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word query)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word 32#64)))
    (code : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source hashCall=(some (.returned value),post)) :
    ∃ hash inner,1≤source.clock ∧
      evaluateHOLFiniteState (QueryBranch.bind {source with clock:=source.clock-1} "h" hash) afterHash=(some (.returned value),inner) ∧
      post=QueryBranch.restore source "h" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "key",localVar "klen"]=
      some [.val (.word query),.val (.word 32#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,keyCell,lengthCell]
  obtain ⟨callee,called,pCell,nCell⟩ := Hash.environment source.code.lookup query code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_normal source post "h" .one (ofString "htab_hash")
    [localVar "key",localVar "klen"] _ Hash.body afterHash callee .one args called value normal
  have shape : shapeOfHOLExact returned=.one := (shapeEqHOL_eq_true _ _).mp (by simpa using checked)
  obtain ⟨hash,valueEq⟩ := Input.RlpWrite.U256Value.scalar_word returned shape
  rw [valueEq] at continued
  have pure:=HashAny32.readonly source.code entry rfl
  rw [bodyRun] at pure
  have frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source := pure
  have clockBound:=evaluateHOLFiniteState_clock_le entry Hash.body
  have priced:=HashAny32.body_cost entry nCell
  rw [bodyRun] at clockBound priced
  change target.clock≤source.clock-1 at clockBound
  change source.clock-1-target.clock≤0 at priced
  have clock : target.clock=source.clock-1 := by omega
  have same:=Input.CallNormal.continuation_of_erase source target "h" (.val (.word hash)) frame
  rw [clock] at same
  change Input.CallNormal.continuationEntry source target "h" (.val (.word hash))=QueryBranch.bind {source with clock:=source.clock-1} "h" hash at same
  rw [same] at continued
  exact ⟨hash,inner,funded,continued,endpoint⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_hash_normal

import InitECandidate.Solver.Rlp.CurrentValidation.AfterHeader

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The same real header parser result advances a continuing flat parse. -/
theorem parse_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending : BitVec 64)
    (data : State source position ending 1#64)
    (normal : evaluateHOLFiniteState source Validation.parse=(none,target)) :
    ∃ next,State target next ending 1#64 ∧ position.toNat<next.toNat ∧ LocalEffects.erase target=LocalEffects.erase source := by
  obtain ⟨paid,answer,inner,minimum,maximum,funded,valid,remaining,endpoint⟩ := Header.scoped_none source target position (ending-position)
    "h" Validation.headerArguments Validation.afterHeader
    (Validation.header_arguments source position ending data.positionCell data.endCell) data.arena.code normal
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,extent,binary,listHeader⟩ := valid
  subst answer
  let entry:=setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have entryData : State entry position ending 1#64 :=
    (data.at_clock (source.clock-paid)).bound_value "h" (Header.result header payload flag) (by decide)
  have hCell : entry.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨next,nextData,advances,frame⟩ := after_header_none entry inner position ending header payload flag entryData hCell positive extent remaining
  have restored:=nextData.restored source "h" (by decide)
  rw [←endpoint] at restored
  refine ⟨next,restored,advances,?_⟩
  rw [endpoint]
  exact frame

theorem at_end_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (ending : BitVec 64)
    (data : State source ending ending 1#64)
    (normal : evaluateHOLFiniteState source Validation.atEnd=(none,target)) :
    State target ending ending 0#64 ∧ LocalEffects.erase target=LocalEffects.erase source := by
  have choice : evaluateHOLFiniteState source Validation.atEnd=evaluateHOLFiniteState source Validation.stop := by
    simp [Validation.atEnd,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,data.topCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have assigned:=StateSteps.assign_execute source "go" (.const 0#64) 1#64 0#64 data.goCell rfl
  change evaluateHOLFiniteState source Validation.stop=(none,bind source "go" 0#64) at assigned
  have same : target=bind source "go" 0#64 := (Prod.mk.inj (normal.symm.trans (choice.trans assigned))).2
  rw [same]
  exact ⟨data.stopped,rfl⟩

/-- Every real continuing body either finishes the flat list or advances
inside its fixed end. The actual unmapped nested push never enters a frame. -/
theorem loop_body_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending : BitVec 64)
    (data : State source position ending 1#64)
    (normal : evaluateHOLFiniteState source Validation.loopBody=(none,target)) :
    ∃ next go,State target next ending go ∧ ending.toNat-next.toNat+go.toNat<ending.toNat-position.toNat+1 ∧
      LocalEffects.erase target=LocalEffects.erase source := by
  have dispatch : evaluateHOLFiniteState source Validation.loopBody=
      if position=ending then evaluateHOLFiniteState source Validation.atEnd else evaluateHOLFiniteState source Validation.parse := by
    simp [Validation.loop_body_shape,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,data.positionCell,data.endCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [dispatch] at normal
  by_cases same : position=ending
  · rw [if_pos same] at normal
    subst position
    have finished:=at_end_none source target ending data normal
    exact ⟨ending,0#64,finished.1,(by simp),finished.2⟩
  · rw [if_neg same] at normal
    obtain ⟨next,nextData,advances,frame⟩ := parse_none source target position ending data normal
    refine ⟨next,1#64,nextData,?_,frame⟩
    change ending.toNat-next.toNat+1<ending.toNat-position.toNat+1
    have before:=nextData.ordered
    omega

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.parse_none
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.at_end_none
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.loop_body_none

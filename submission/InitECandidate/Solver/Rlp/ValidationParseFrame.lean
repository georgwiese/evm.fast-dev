import InitECandidate.Solver.Rlp.ValidationAfterHeaderFrame
import InitECandidate.Solver.Rlp.ValidationBodyCost

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem parse_none_above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source parse=(none,target)) :
    ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Above source target cursor.toNat := by
  obtain ⟨paid,answer,inner,minimum,maximum,funded,valid,continuation,restored⟩ := Header.scoped_none source target position (ending-position) "h" headerArguments afterHeader
    (header_arguments source position ending view.positionCell view.endCell) installed normal
  obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := valid
  rw [same] at continuation
  let ready := setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have other (name : String) (different : ofString name≠ofString "h") :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have readyView : View ready rootEnd cursor limit position ending 1#64 frames :=
    View.of_fields source ready rootEnd cursor limit position ending 1#64 frames view rfl rfl rfl
      ((other "pos" (by decide)).trans view.positionCell) ((other "end" (by decide)).trans view.endCell)
      ((other "top" (by decide)).trans view.topCell) ((other "go" (by decide)).trans view.goCell)
  have hCell : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨nextCursor,nextArena,smaller,above⟩ := after_header_none_above ready inner rootEnd cursor limit position ending header payload flag frames readyView hCell installed continuation
  refine ⟨nextCursor,Arena.of_fields inner target nextCursor limit nextArena ?_ ?_,smaller,?_⟩
  · rw [restored]; rfl
  · rw [restored]; rfl
  · intro query upper
    rw [restored]
    exact above query upper

theorem at_end_readonly (code) : Input.LocalEffects.Preserves code atEnd := by
  simp only [atEnd,stop,pop]
  exact Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.assign code _ _)
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _)
      (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _)))

theorem loop_body_none_above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Above source target cursor.toNat := by
  have dispatch : evaluateHOLFiniteState source loopBody=
      if position=ending then evaluateHOLFiniteState source atEnd else evaluateHOLFiniteState source parse := by
    simp [loop_body_shape,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,view.positionCell,view.endCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [dispatch] at normal
  by_cases same : position=ending
  · rw [if_pos same] at normal
    have fields := at_end_readonly source.code source rfl
    rw [normal] at fields
    have domain := congrArg PanSemStateFiniteExact.memaddrs fields
    have globals := congrArg PanSemStateFiniteExact.globals fields
    have memory := congrArg PanSemStateFiniteExact.memory fields
    exact ⟨cursor,Arena.of_fields source target cursor limit view.arena domain globals,Nat.le_refl _,fun query _=>congrFun memory query⟩
  · rw [if_neg same] at normal
    exact parse_none_above source target rootEnd cursor limit position ending frames view installed normal

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.parse_none_above
#print axioms InitECandidate.Solver.Rlp.Validation.at_end_readonly
#print axioms InitECandidate.Solver.Rlp.Validation.loop_body_none_above

import InitECandidate.Solver.Headers.CurrentValidate.Nonlocal
import InitECandidate.Solver.Headers.CurrentValidate.Increment
import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.Input.ScopedNoLoopControl
import InitECandidate.Solver.Input.ScopedCallNoneData

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def linkFirst : ExpHOL 64 := match linkArguments with | first::_=>first | _=>.const 0#64
def linkSecond : ExpHOL 64 := match linkArguments with | _::second::_=>second | _=>.const 0#64
theorem link_arguments : linkArguments=[linkFirst,linkSecond,.const 32#64] := rfl

theorem after_link_guarded : Input.GuardedCounter 1 afterLink := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,linkShape⟩ := shapes
  rw [linkShape]
  exact .checks (.ite _ (.raised _ _) .skip) .increment

theorem link_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source linkStep).2.clock≤129 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,linkShape,_⟩ := shapes
  rw [linkShape,link_arguments]
  exact MutableTable.MemeqAny.scoped_cost source linkFirst linkSecond (ofString "eq") afterLink
    (MutableTable.MemeqAny.original_code source.code installed)
    (Input.ClockCost.of_quiet source.code afterLink (after_link_guarded.quiet source.code))

theorem link_step_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code linkStep := by
  obtain ⟨_,_,_,_,_,_,_,_,_,linkShape,afterShape⟩ := shapes
  rw [linkShape]
  apply Input.LocalEffects.scoped_body code (ofString "eq") .one (ofString "memeq") linkArguments afterLink Memeq32.formals Memeq32.body .one
    (MutableTable.MemeqAny.original_code code installed) (MutableTable.MemeqAny.readonly code)
  rw [afterShape]
  exact Input.LocalEffects.sequence code _ _
    (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.skip code))
    (Input.LocalEffects.assign code _ _)

theorem link_step_no_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source linkStep).1≠some .break ∧ (evaluateHOLFiniteState source linkStep).1≠some .continue := by
  obtain ⟨_,_,_,_,_,_,_,_,_,linkShape,_⟩ := shapes
  rw [linkShape]
  exact Input.scoped_no_loop_control _ _ _ _ _ after_link_guarded.no_control source

/-- A genuine normal comparison iteration retains the entire current
context and advances its original caller counter. No header-pointer read or
comparison success is presupposed. -/
theorem link_step_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (normal : evaluateHOLFiniteState source linkStep=(none,post)) :
    RoundState data origin post (index+1) := by
  have frame:=link_step_readonly source.code state.arena.code source rfl
  rw [normal] at frame
  obtain ⟨_,_,_,_,_,_,_,_,_,linkShape,_⟩ := shapes
  rw [linkShape] at normal
  obtain ⟨funded,values,body,callee,shape,target,value,inner,args,called,bodyRun,checked,continued,endpoint⟩ :=
    Input.CallNormal.scoped_none_data source post "eq" .one (ofString "memeq") linkArguments afterLink normal
  let ready:=Input.CallNormal.continuationEntry source target "eq" value
  have lookup (key : String) (different : ofString key≠ofString "eq") : ready.locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  have current : ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := (lookup "i" (by decide)).trans state.indexCell
  have innerEq:=after_link_guarded.normal ready inner (BitVec.ofNat 64 index) current continued
  have finalLookup (key : String) (notEq : ofString key≠ofString "eq") (notIndex : ofString "i"≠ofString key) :
      post.locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    rw [endpoint,innerEq,restore_lookup_other source _ "eq" key notEq,bind_lookup_other ready "i" key _ notIndex]
    exact lookup key notEq
  apply state.nonlocal data origin source post index (index+1) frame
  · exact (finalLookup "arr" (by decide) (by decide)).trans state.arrayCell
  · exact (finalLookup "n" (by decide) (by decide)).trans state.countCell
  · exact (finalLookup "hs" (by decide) (by decide)).trans state.hsCell
  · exact (finalLookup "hashes" (by decide) (by decide)).trans state.hashesCell
  · rw [endpoint,innerEq,restore_lookup_other source _ "eq" "i" (by decide),bind_lookup_same]
    simp [BitVec.ofNat_add]

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_arguments
#print axioms InitECandidate.Solver.Headers.CurrentValidate.after_link_guarded
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_step_cost
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_step_readonly
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_step_no_control
#print axioms InitECandidate.Solver.Headers.CurrentValidate.link_step_normal

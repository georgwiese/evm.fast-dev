import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual original allocation assigning an existing caller local, as used
when payload hashing reuses its roots binding. Its own observed normal
return derives request room, clock funding and the exact assigned state. -/
theorem local_call_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (old pointer amount : BitVec 64)
    (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values amount))
    (code : source.code.lookup (ofString "alloc")=some (formals,body,.one))
    (trapCode : source.code.lookup (ofString "trap_with")=some (Input.Trap.formals,Input.Trap.body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "alloc") arguments)=(none,target)) :
    pointer.toNat+amount.toNat≤2952790016 ∧ 1≤source.clock ∧
      target=bind (post {source with clock:=source.clock-1} pointer amount) name pointer := by
  obtain ⟨callee,called,n⟩ := environment source.code.lookup amount code
  obtain ⟨positive,actualPost,returned,bodyRun⟩ := Input.CallNormal.assigned_callee_return source target (some (.local,ofString name)) (ofString "alloc") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨returnedEq,room,frame⟩ := post_of_normal entry actualPost pointer amount n heap bounded trapCode returned bodyRun
  rw [returnedEq] at bodyRun
  have valid : isValidValueHOLFinite source .local (ofString name) (.val (.word pointer))=true := by
    simp [isValidValueHOLFinite,lookupKvarHOLFinite,present,shapeOfHOLExact,shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none (ofString "alloc") arguments _ body callee .one
    (.val (.word pointer)) actualPost args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
    (by simpa only [isValidValueHOLFinite_eq] using valid)
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F=>{state with locals:=source.locals}) frame
  change {actualPost with locals:=source.locals}=post {source with clock:=source.clock-1} pointer amount at callerFrame
  rw [callerFrame] at actual
  have same := congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨room,positive,same⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.local_call_normal

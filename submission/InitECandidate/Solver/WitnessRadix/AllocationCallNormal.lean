import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A normal original scoped allocation derives its actual request room,
call clock and continuation state. This applies only at a reached allocation;
unused conditional allocation paths require no room premise. -/
theorem call_normal {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values amount))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation) = (some (.returned value), target)) :
    pointer.toNat + amount.toNat ≤ 2952790016 ∧ 1 ≤ source.clock ∧
      ∃ inner, evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind (post {source with clock := source.clock - 1} pointer amount) name pointer) continuation =
        (some (.returned value), inner) ∧ target = restore source name inner := by
  have positive := Input.CallNormal.normal_clock source target (ofString name) .one (ofString "alloc") arguments continuation value normal
  obtain ⟨callee, called, amountLocal⟩ := environment source.code.lookup amount code
  obtain ⟨calleeTarget, returned, bodyRun⟩ := Input.CallNormal.callee_return source target (ofString name) .one (ofString "alloc") arguments (values amount)
    body continuation callee .one args called positive value normal
  have room := room_of_normal (callEntryStateHOLFinite source callee) calleeTarget pointer amount amountLocal heapGlobal pointerBound trapCode returned bodyRun
  have actual := call_execute source name arguments continuation pointer amount args code heapGlobal room positive
  have joined := actual.symm.trans normal
  let ready := WitnessRadix.QueryBranch.bind (post {source with clock := source.clock - 1} pointer amount) name pointer
  let inner := (evaluateHOLFiniteState ready continuation).2
  have resultEq := congrArg Prod.fst joined
  have stateEq := congrArg Prod.snd joined
  refine ⟨room, positive, inner, Prod.ext resultEq rfl, ?_⟩
  exact stateEq.symm

/-- A genuinely returning allocator must have read a scalar request from
its first guard. This derives its argument type even for arbitrary locals. -/
theorem amount_word_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ amount : BitVec 64,source.locals.lookup (ofString "n")=some (.val (.word amount)) := by
  rw [body_shape] at normal
  have pointerRead : eval source heapVar=some (.val (.word pointer)) := by
    simp [eval,heapVar,evalHOLExact,toExact,heapGlobal]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "p" heapVar pointer pTail value pointerRead normal
  let entered:=WitnessRadix.QueryBranch.bind source "p" pointer
  have pLocal : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : entered.locals.lookup (ofString "n")=source.locals.lookup (ofString "n") :=
    bind_lookup_other source "p" "n" pointer (by decide)
  have safe : Input.LocalPrefix (ofString "n") firstGuard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,firstRun,back,kept⟩:=safe.normal_continue entered inner
    (.dec (ofString "q") .one roundExpression qTail) value continued
  cases request : source.locals.lookup (ofString "n") with
  | none=>
    simp [firstGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,toExact,localVar,
      pLocal,nLocal,request,valueIsWord,valueWord,wordOpHOL,wordOp] at firstRun
  | some requestValue=>
    cases requestValue with
    | rStruct fields=>
      simp [firstGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,toExact,localVar,
        pLocal,nLocal,request,valueIsWord,valueWord,wordOpHOL,wordOp] at firstRun
    | nStruct name fields=>
      simp [firstGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,toExact,localVar,
        pLocal,nLocal,request,valueIsWord,valueWord,wordOpHOL,wordOp] at firstRun
    | val payload=>
      cases payload with
      | word amount=>exact ⟨amount,rfl⟩

/-- The actual allocator's guards retain every incoming valid heap frontier
on a genuine return. Failed calls require no heap or future-success assertion. -/
theorem normal_heap (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Returning code body := by
  intro source codeEq lower initial value returned
  obtain ⟨pointer,heapGlobal,lowerBound,upperBound,aligned⟩:=initial
  let target:=(evaluateHOLFiniteState source body).2
  have normal : evaluateHOLFiniteState source body=(some (.returned value),target) := Prod.ext returned rfl
  obtain ⟨amount,amountLocal⟩:=amount_word_of_normal source target pointer heapGlobal value normal
  have trapCode : source.code.lookup (ofString "trap_with")=some (Input.Trap.formals,Input.Trap.body,.one) := by
    rw [codeEq]
    exact Input.Trap.original_code code installed
  obtain ⟨answer,room,frame⟩:=post_of_normal source target pointer amount amountLocal heapGlobal upperBound trapCode value normal
  have checked:=guards pointer amount room
  have heapCell:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) frame
  change target.globals.lookup (ofString "heap_ptr")=(post source pointer amount).globals.lookup (ofString "heap_ptr") at heapCell
  have stored : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (rounded pointer amount))) := by
    simpa [post,HolFiniteMapExact.update,FUPDATE] using heapCell
  refine ⟨rounded pointer amount,stored,?_,checked.2.2.2.1,checked.2.2.2.2⟩
  have growth:=checked.2.2.1
  omega

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_normal

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.amount_word_of_normal
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.normal_heap

import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.WitnessRadix.AllocationEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationRoundedExpected
import InitECandidate.Solver.Input.AssignedCallNormal
import InitECandidate.Solver.Input.GlobalAssign

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual allocation assigning an existing scalar global, as used by the
original journal/state initialization. Normal execution derives room, clock
funding and the exact full caller state. -/
theorem global_call_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (old pointer amount : BitVec 64)
    (present : source.globals.lookup (ofString name) = some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values amount))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 2952790016)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global, ofString name), none)) (ofString "alloc") arguments) = (none, target)) :
    pointer.toNat + amount.toNat ≤ 2952790016 ∧ 1 ≤ source.clock ∧
      target = Input.putGlobal (post {source with clock := source.clock - 1} pointer amount) name pointer := by
  obtain ⟨callee, called, n⟩ := environment source.code.lookup amount code
  obtain ⟨positive, actualPost, returned, bodyRun⟩ := Input.CallNormal.assigned_callee_return source target (some (.global, ofString name)) (ofString "alloc") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨returnedEq, room, frame⟩ := post_of_normal entry actualPost pointer amount n heap bounded trapCode returned bodyRun
  rw [returnedEq] at bodyRun
  have valid : isValidValueHOLFinite source .global (ofString name) (.val (.word pointer)) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, present, shapeOfHOLExact, shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .global (ofString name) none (ofString "alloc") arguments _ body callee .one
    (.val (.word pointer)) actualPost args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
    (by simpa only [isValidValueHOLFinite_eq] using valid)
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  change {actualPost with locals := source.locals} = post {source with clock := source.clock - 1} pointer amount at callerFrame
  rw [callerFrame] at actual
  have same := congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨room, positive, same⟩

theorem global_call_normal_expected {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (old : BitVec 64)
    (pointer amount next : Nat) (pointerBound : pointer ≤ 2952790016) (amountSmall : amount < 2 ^ 64)
    (lower : pointer + amount ≤ next) (upper : next < pointer + amount + 8) (aligned : next % 8 = 0)
    (present : source.globals.lookup (ofString name) = some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values (BitVec.ofNat 64 amount)))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 pointer))))
    (normal : evaluateHOLFiniteState source (.call (some (some (.global, ofString name), none)) (ofString "alloc") arguments) = (none, target)) :
    pointer + amount ≤ 2952790016 ∧ next ≤ 2952790016 ∧ 1 ≤ source.clock ∧
      target = Input.putGlobal {source with globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 next))), clock := source.clock - 1}
        name (BitVec.ofNat 64 pointer) := by
  have pointerNat : (BitVec.ofNat 64 pointer).toNat = pointer := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have amountNat : (BitVec.ofNat 64 amount).toNat = amount := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt amountSmall]
  obtain ⟨room, positive, same⟩ := global_call_normal source target name old (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) present arguments args code trapCode heap (by rw [pointerNat]; exact pointerBound) normal
  have rounded := rounded_expected (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) next
    (by rw [pointerNat, amountNat]; omega) (by rw [pointerNat, amountNat]; exact lower) (by rw [pointerNat, amountNat]; exact upper) aligned
  have nextBound := (guards (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) room).2.2.2.1
  rw [rounded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at nextBound
  refine ⟨by simpa only [pointerNat, amountNat] using room, nextBound, positive, ?_⟩
  simpa only [post, rounded] using same

/-- A real normal global-result allocation derives its exact caller state
without requiring the destination's old value as an entry premise. Invalid
destination shapes cannot produce the observed normal continuation. -/
theorem global_call_normal_any {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (pointer amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments=some (values amount))
    (code : source.code.lookup (ofString "alloc")=some (formals,body,.one))
    (trapCode : source.code.lookup (ofString "trap_with")=some (Input.Trap.formals,Input.Trap.body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments)=(none,target)) :
    pointer.toNat+amount.toNat≤2952790016 ∧ 1≤source.clock ∧
      target=Input.putGlobal (post {source with clock:=source.clock-1} pointer amount) name pointer := by
  classical
  obtain ⟨callee,called,nCell⟩ := environment source.code.lookup amount code
  obtain ⟨positive,actualPost,returned,bodyRun⟩ := Input.CallNormal.assigned_callee_return source target
    (some (.global,ofString name)) (ofString "alloc") arguments _ body callee .one args called normal
  obtain ⟨answer,room,frame⟩ := post_of_normal (callEntryStateHOLFinite source callee) actualPost pointer amount nCell heap bounded trapCode returned bodyRun
  rw [answer] at bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F=>{state with locals:=source.locals}) frame
  change {actualPost with locals:=source.locals}=post {source with clock:=source.clock-1} pointer amount at callerFrame
  rw [evaluateHOLFiniteState_call,args] at normal
  simp only [called,if_neg (show source.clock≠0 by omega),bodyRun,shapeOfHOLExact,shapeEqHOL,↓reduceIte] at normal
  split at normal
  · have targetEq := (congrArg Prod.snd normal).symm
    change target=setKvarHOLFinite .global (ofString name) (.val (.word pointer)) {actualPost with locals:=source.locals} at targetEq
    refine ⟨room,positive,?_⟩
    rw [targetEq,callerFrame]
    rfl
  · cases normal

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.global_call_normal
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.global_call_normal_expected

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.global_call_normal_any

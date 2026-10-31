import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.Input.ScopedCallContinuing

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem call_continuing {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values amount))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 2952790016)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation) = (none, target)) :
    pointer.toNat + amount.toNat ≤ 2952790016 ∧ 1 ≤ source.clock ∧
      ∃ inner, evaluateHOLFiniteState (bind (post {source with clock := source.clock - 1} pointer amount) name pointer) continuation = (none, inner) ∧
        target = restore source name inner := by
  obtain ⟨callee, called, binding⟩ := environment source.code.lookup amount code
  obtain ⟨positive, actual, returned, inner, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_continuing source target name .one (ofString "alloc") arguments (values amount) body continuation callee .one args called normal
  have room := room_of_normal (callEntryStateHOLFinite source callee) actual pointer amount binding heap bounded trapCode returned bodyRun
  have executed := call_execute source name arguments continuation pointer amount args code heap room positive
  have joined := executed.symm.trans normal
  let ready := bind (post {source with clock := source.clock - 1} pointer amount) name pointer
  have resultEq := congrArg Prod.fst joined
  have stateEq := congrArg Prod.snd joined
  exact ⟨room, positive, (evaluateHOLFiniteState ready continuation).2, Prod.ext resultEq rfl, stateEq.symm⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_continuing

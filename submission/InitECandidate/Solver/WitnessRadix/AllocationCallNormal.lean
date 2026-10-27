import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.Input.NormalCallClock

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

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_normal

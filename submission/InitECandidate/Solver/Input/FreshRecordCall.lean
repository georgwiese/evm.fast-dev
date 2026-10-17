import InitECandidate.Solver.Input.FreshRecord
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.FreshRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {F : Type}

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (kind : Kind)
    (known : table (ofString (functionName kind)) = some ([], body kind, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString (functionName kind)) [] = some (body kind, callee, .one) := by
  have raw : lookupCodeHOLExact table (ofString (functionName kind)) [] = some (body kind, fun _ => none, .one) := by
    simp [lookupCodeHOLExact, known]
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString (functionName kind)) [] (body kind) (fun _ => none) .one raw
  exact ⟨callee, called⟩

/-- Actual te_new/msg_new caller. Each initializes its complete allocation to
zero and consumes10source clocks including the outer call. -/
theorem call_execute (source : PanSemStateFiniteExact 64 F) (kind : Kind)
    (name : String) (continuation : ProgHOL 64) (pointer : BitVec 64)
    (known : source.code.lookup (ofString (functionName kind)) = some ([], body kind, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + size kind ≤ 33806089496)
    (mapped : ∀ offset, offset + 8 ≤ size kind → offset % 8 = 0 → source.memaddrs (WitnessRadix.byteAddress pointer offset))
    (enough : 10 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName kind)) [] continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind
        {WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind)) with
          memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
          clock := source.clock - 10} name pointer) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called⟩ := environment source.code.lookup kind known
  let entry := callEntryStateHOLFinite source callee
  have bodyRun := execute entry kind pointer heap code zeroCode aligned room mapped (by change 9 ≤ source.clock - 1; omega)
  have frame := canonical entry kind pointer
  have actual := Input.CallNormal.return_execute source (closed entry kind pointer) name .one (ofString (functionName kind)) [] []
    (body kind) continuation callee .one (.val (.word pointer)) rfl called (by omega) bodyRun
    (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - 9 = source.clock - 10 := by omega
  have restored : {closed entry kind pointer with locals := source.locals} =
      {WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind)) with
        memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
        clock := source.clock - 10} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, WitnessRadix.PersistentAlloc.post, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 F =>
    setVarHOLFinite (ofString name) (.val (.word pointer)) state) restored
  change Input.CallNormal.continuationEntry source (closed entry kind pointer) name (.val (.word pointer)) = _ at nextEq
  rw [nextEq] at actual
  exact actual

/-- Exact heap extent, with no alignment padding for these two actual sizes. -/
theorem heap_geometry (kind : Kind) (pointer : BitVec 64) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + size kind ≤ 33806089496) :
    (WitnessRadix.PersistentAlloc.rounded pointer (BitVec.ofNat 64 (size kind))).toNat = pointer.toNat + size kind := by
  have amount : (BitVec.ofNat 64 (size kind)).toNat = size kind := by cases kind <;> decide
  have multiple : size kind % 8 = 0 := by cases kind <;> decide
  have number := WitnessRadix.PersistentAlloc.rounded_nat pointer (BitVec.ofNat 64 (size kind)) (by rw [amount]; omega)
  rw [number, amount]
  omega

/-- The complete persistent-record clear preserves both earlier allocations
and all later heap locations. -/
theorem memory_outside (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer query : BitVec 64)
    (room : pointer.toNat + size kind ≤ 33806089496)
    (outside : query.toNat < pointer.toNat ∨ pointer.toNat + size kind ≤ query.toNat) :
    (closed source kind pointer).memory query = source.memory query := by
  apply memory_away
  intro offset inside same
  have number := WitnessRadix.byteAddress_toNat pointer offset (by omega)
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  rcases outside with below | high <;> omega

end InitECandidate.Solver.Input.FreshRecord

#print axioms InitECandidate.Solver.Input.FreshRecord.environment
#print axioms InitECandidate.Solver.Input.FreshRecord.call_execute
#print axioms InitECandidate.Solver.Input.FreshRecord.heap_geometry
#print axioms InitECandidate.Solver.Input.FreshRecord.memory_outside

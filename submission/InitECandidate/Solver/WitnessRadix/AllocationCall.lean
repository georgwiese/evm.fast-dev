import InitECandidate.Solver.WitnessRadix.AllocationEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationArithmetic

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual lexical allocation call, including the call clock, returned
pointer binding, updated heap global and restoration after the continuation. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (values amount))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (fits : pointer.toNat + amount.toNat ≤ 2952790016) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation) =
      (let output := evaluateHOLFiniteState (bind (post { source with clock := source.clock - 1 } pointer amount) name pointer) continuation;
       (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, lookup, amountLocal⟩ := environment source.code.lookup amount code
  let entry := callEntryStateHOLFinite source callee
  have guards := guards pointer amount fits
  obtain ⟨target, bodyRun, frame⟩ := execute entry pointer amount amountLocal heapGlobal guards.1 guards.2.1
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := target.locals }) frame
  have targetEq : target = { post entry pointer amount with locals := target.locals } := by
    simpa only [emptyLocalsHOLFinite] using updated
  have clockEq : target.clock = source.clock - 1 := by
    have clock := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
    exact clock
  have noIncrease : ¬ source.clock - 1 < target.clock := by omega
  have positive : source.clock ≠ 0 := by omega
  rw [evaluateHOLFiniteState_decCall_total]
  simp only [args, lookup, if_neg positive]
  rw [bodyRun]
  simp only [shapeOfHOLExact, shapeEqHOL, Bool.and_self, ↓reduceIte]
  simp only [fixClockHOLFinite, entry, callEntryStateHOLFinite, noIncrease, ↓reduceIte]
  rw [targetEq]
  rfl

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_execute

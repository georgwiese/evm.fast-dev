import InitECandidate.Solver.WitnessRadix.TableEnvironment

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def callState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  bind { source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (plan.table + 72 + 57 * plan.capacity + plan.padding))))
    memory := resultMemory source.memory source.be plan
    clock := source.clock - (price plan.capacity + 1) } name (BitVec.ofNat 64 plan.table)

/-- The actual htab_new lexical call, with concrete memory/heap result,
actual code/argument lookup, exact source-clock cost and caller restoration. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (values plan.capacity))
    (code : source.code.lookup (ofString "htab_new") = some (formals, body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price plan.capacity + 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation) =
      (let output := evaluateHOLFiniteState (callState source name plan) continuation;
       (output.1, restore source name output.2)) := by
  classical
  obtain ⟨callee, lookup, keyLocal, capLocal⟩ := environment source.code.lookup plan.capacity code
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, bodyRun, bodyFrame⟩ := execute entry plan ready domain capacityShape keyLocal capLocal heapGlobal allocCode zeroCode
    (by change price plan.capacity ≤ source.clock - 1; omega)
  have frame := bodyFrame.trans (entered_frame entry plan)
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := target.locals }) frame
  have targetEq : target = { entry with
      locals := target.locals
      globals := entry.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (plan.table + 72 + 57 * plan.capacity + plan.padding))))
      memory := resultMemory entry.memory entry.be plan
      clock := entry.clock - price plan.capacity } := by
    simpa only [emptyLocalsHOLFinite] using updated
  have clockEq : target.clock = source.clock - 1 - price plan.capacity := congrArg (fun state => state.clock) frame
  have noIncrease : ¬ source.clock - 1 < target.clock := by omega
  have positive : source.clock ≠ 0 := by omega
  have noIncreasePaid : ¬ source.clock - 1 < source.clock - (price plan.capacity + 1) := by omega
  have clockSub : source.clock - 1 - price plan.capacity = source.clock - (price plan.capacity + 1) := by omega
  rw [evaluateHOLFiniteState_decCall_total]
  simp only [args, lookup, if_neg positive]
  rw [bodyRun]
  simp only [shapeOfHOLExact, shapeEqHOL, Bool.and_self, ↓reduceIte]
  simp only [fixClockHOLFinite, noIncrease, ↓reduceIte]
  rw [targetEq]
  simp only [entry, callEntryStateHOLFinite, clockSub, noIncreasePaid, ↓reduceIte, callState, QueryBranch.bind, setVarHOLFinite, restore]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.call_execute

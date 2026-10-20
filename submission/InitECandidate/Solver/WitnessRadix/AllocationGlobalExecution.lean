import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.WitnessRadix.AllocationExpected
import InitECandidate.Solver.Input.GlobalAssign

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Sufficient current room and a scalar destination execute the genuine
global-result allocator caller in exactly one source tick. -/
theorem global_call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String)
    (old pointer amount : BitVec 64)
    (present : source.globals.lookup (ofString name) = some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values amount))
    (code : source.code.lookup (ofString "alloc") = some (formals,body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (room : pointer.toNat + amount.toNat ≤ 33806089496) (positive : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments) =
      (none,Input.putGlobal (post {source with clock := source.clock - 1} pointer amount) name pointer) := by
  obtain ⟨callee,called,amountLocal⟩ := environment source.code.lookup amount code
  let entry := callEntryStateHOLFinite source callee
  have checked := guards pointer amount room
  obtain ⟨target,bodyRun,frame⟩ := execute entry pointer amount amountLocal heap checked.1 checked.2.1
  have valid : isValidValueHOLFinite source .global (ofString name) (.val (.word pointer)) = true := by
    simp [isValidValueHOLFinite,lookupKvarHOLFinite,present,shapeOfHOLExact,shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .global (ofString name) none (ofString "alloc") arguments _ body callee .one
    (.val (.word pointer)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL]) (by simpa only [isValidValueHOLFinite_eq] using valid)
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  change {target with locals := source.locals} = post {source with clock := source.clock - 1} pointer amount at callerFrame
  rw [callerFrame] at actual
  exact actual

theorem global_call_execute_expected {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (old : BitVec 64)
    (pointer amount next : Nat) (room : pointer + amount ≤ 33806089496)
    (lower : pointer + amount ≤ next) (upper : next < pointer + amount + 8) (aligned : next % 8 = 0)
    (present : source.globals.lookup (ofString name) = some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values (BitVec.ofNat 64 amount)))
    (code : source.code.lookup (ofString "alloc") = some (formals,body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 pointer))))
    (positive : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments) =
      (none,Input.putGlobal {source with globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 next))),clock := source.clock - 1}
        name (BitVec.ofNat 64 pointer)) := by
  have pointerNum : (BitVec.ofNat 64 pointer).toNat = pointer := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have amountNum : (BitVec.ofNat 64 amount).toNat = amount := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have actual := global_call_execute source name old (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) present arguments args code heap (by rw [pointerNum,amountNum]; exact room) positive
  have rounded := rounded_expected (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) next
    (by rw [pointerNum,amountNum]; omega) (by rw [pointerNum,amountNum]; exact lower) (by rw [pointerNum,amountNum]; exact upper) aligned
  simpa only [post,rounded] using actual

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.global_call_execute

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.global_call_execute_expected

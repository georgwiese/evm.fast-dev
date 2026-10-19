import InitECandidate.Solver.Mpt.StorageSetProgram
import InitECandidate.Solver.WitnessRadix.Bindings
import InitECandidate.Solver.WitnessRadix.TableEnvironment
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

set_option maxRecDepth 100000 in
theorem new_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_new") = some (TableNew.formals,TableNew.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 116 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,TableNew.body,TableNew.formals,Guest.guestFn_htab_new,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem present_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag value : BitVec 64)
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair flag value)) (present : flag ≠ 0#64) :
    evaluateHOLFiniteState source afterGet =
      (let output := evaluateHOLFiniteState (bind source "inner" value) allocate
       (output.1,restore source "inner" output.2)) := by
  classical
  let entered := bind source "inner" 0#64
  have enteredPair : entered.locals.lookup (ofString "m") = some (Get.pair flag value) :=
    (bind_lookup_other source "inner" "m" 0#64 (by decide)).trans pairLocal
  have read : eval entered (.rfield 1 (localVar "m")) = some (.val (.word value)) := by
    simp [eval,evalHOLExact,localVar,toExact,enteredPair,Get.pair]
  have overwrite : bind entered "inner" value = bind source "inner" value := by
    have maps : (source.locals.update (ofString "inner",.val (.word 0#64))).update (ofString "inner",.val (.word value)) =
        source.locals.update (ofString "inner",.val (.word value)) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "inner" = query <;> simp [HolFiniteMapExact.update,FUPDATE,same]
    exact congrArg (fun locals => {source with locals := locals}) maps
  have assignRun := StateSteps.assign_execute entered "inner" (.rfield 1 (localVar "m")) 0#64 value (bind_lookup_same _ _ _) read
  have chooseRun : evaluateHOLFiniteState entered choose = (none,bind source "inner" value) := by
    rw [choose,evaluateHOLFiniteState_ite]
    simp only [evalHOLExact,localVar,toExact,enteredPair,Get.pair,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.map_some]
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,beq_iff_eq,present,↓reduceIte]
    rw [overwrite] at assignRun
    exact assignRun
  have tail := StateSteps.next_sequence entered (bind source "inner" value) choose allocate chooseRun (Nat.le_refl _)
  rw [afterGet,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
  change (let output := evaluateHOLFiniteState entered (.seq choose allocate); (output.1,restore source "inner" output.2)) = _
  rw [tail]

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.new_code
#print axioms InitECandidate.Solver.Mpt.StorageSet.present_dispatch

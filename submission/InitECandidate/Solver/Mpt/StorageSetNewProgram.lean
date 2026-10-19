import InitECandidate.Solver.Mpt.StorageSetDispatch
import InitECandidate.Solver.Mpt.TableNewAssigned

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def newBranch : ProgHOL 64 := .seq (.seq newCall publishCall) allocate

def newProperty {ι : Type} (property : ι → BitVec 64 → Prop) (outer : ι) (cursor : Nat) (index : Option ι) (value : BitVec 64) : Prop :=
  TableNewOwnership.liftProperty property (fun pointer => AllocatedBytes.Arena pointer 32 ∧ pointer.toNat % 8 = 0) index value ∨
    index = some outer ∧ value = BitVec.ofNat 64 cursor

theorem absent_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair 0#64 value)) :
    evaluateHOLFiniteState source afterGet =
      (let output := evaluateHOLFiniteState (bind source "inner" 0#64) newBranch
       (output.1,restore source "inner" output.2)) := by
  classical
  let entered := bind source "inner" 0#64
  have enteredPair : entered.locals.lookup (ofString "m") = some (Get.pair 0#64 value) :=
    (bind_lookup_other source "inner" "m" 0#64 (by decide)).trans pairLocal
  have selected : evaluateHOLFiniteState entered choose = evaluateHOLFiniteState entered (.seq newCall publishCall) := by
    rw [choose,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,localVar,toExact,enteredPair,Get.pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have tail : evaluateHOLFiniteState entered (.seq choose allocate) = evaluateHOLFiniteState entered newBranch := by
    simp only [newBranch,evaluateHOLFiniteState_seq_line780,selected]
  rw [afterGet,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
  change (let output := evaluateHOLFiniteState entered (.seq choose allocate); (output.1,restore source "inner" output.2)) = _
  rw [tail]

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.absent_dispatch

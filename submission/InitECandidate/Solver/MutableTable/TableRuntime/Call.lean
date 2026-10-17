import InitECandidate.Solver.MutableTable.TableRuntime.Environment
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix
open NaturalLayout

def callState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (kind : KeyHash.Kind) (start capacity : Nat) :=
  WitnessRadix.QueryBranch.bind {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
    memory := (resultMemory source.memory source.be kind start capacity)
    clock := source.clock - (price capacity + 1)} name (BitVec.ofNat 64 start)

/-- Actual original htab_new scoped caller at every original key width.
Derives the complete memory, heap cursor, call clock and lexical restoration;
no constructor result or helper execution is a premise. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind capacity))
    (code : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price capacity + 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation) =
      (let output := evaluateHOLFiniteState (callState source name kind start capacity) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, keyLocal, capLocal⟩ := environment source.code.lookup kind capacity code
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, bodyRun, bodyFrame⟩ := execute entry kind start capacity valid domain capacityShape keyLocal capLocal heapGlobal allocCode zeroCode
    (by change price capacity ≤ source.clock - 1; omega)
  have frame := bodyFrame.trans (entered_frame entry kind start capacity)
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  have clockSub : source.clock - 1 - price capacity = source.clock - (price capacity + 1) := by omega
  have restored : {target with locals := source.locals} = {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
      memory := (resultMemory source.memory source.be kind start capacity)
      clock := source.clock - (price capacity + 1)} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, clockSub] using updated
  have resumed : Input.CallNormal.continuationEntry source target name (.val (.word (BitVec.ofNat 64 start))) = callState source name kind start capacity := by
    rw [Input.CallNormal.continuationEntry, restored]
    rfl
  have actual := Input.CallNormal.return_execute source target name .one (ofString "htab_new") arguments (values kind capacity)
    TableNew.body continuation callee .one (.val (.word (BitVec.ofNat 64 start))) args called (by omega) bodyRun
    (by simp [shapeOfHOLExact, shapeEqHOL])
  rw [resumed] at actual
  exact actual

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.call_execute

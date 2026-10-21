import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def delivered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) :=
  bind (bind source "result" node) "mode" 0#64

theorem terminal_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node oldResult oldMode : BitVec 64)
    (decodedCell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),.val (.word node)]))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source decodeTerminal=(none,delivered source node) := by
  have read : eval source (decodeField 1)=some (.val (.word node)):=by
    simp [eval,decodeField,evalHOLExact,localVar,toExact,decodedCell]
  have first:=StateSteps.assign_execute source "result" (decodeField 1) oldResult node resultCell read
  have nextMode : (bind source "result" node).locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other source "result" "mode" node (by decide)).trans modeCell
  have last:=StateSteps.assign_execute (bind source "result" node) "mode" (.const 0#64) oldMode 0#64 nextMode rfl
  rw [terminal_shape,StateSteps.next_sequence _ _ _ _ first (Nat.le_refl _),last]
  rfl

theorem delivered_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) :
    (delivered source node).locals.lookup (ofString "result")=some (.val (.word node)) ∧
      (delivered source node).locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
      (delivered source node).memory=source.memory ∧ (delivered source node).globals=source.globals ∧ (delivered source node).clock=source.clock :=
  ⟨(bind_lookup_other _ "mode" "result" 0#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,rfl,rfl,rfl⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.terminal_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.delivered_fields

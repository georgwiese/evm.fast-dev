import InitECandidate.Solver.GasBudget.MemoryExpansionCostCharged
import InitECandidate.Solver.GasBudget.StackPopsValues

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_op_revert with | .function fn => progToHOL fn.body | _ => .skip
def outputAddress : ExpHOL 64 := .op .add [frameLoad 24#64, localVar "s"]
def stores : ProgHOL 64 := .seq (.store (frameAddress 120#64) outputAddress)
  (.seq (.store (frameAddress 128#64) (localVar "n")) (.seq (.raise (ofString "EvmErr") (.const 1#64)) MemoryExtend.returnZero))
def afterSize : ProgHOL 64 := .decCall (ofString "s") .one (ofString "sat_word") [localVar "start"] stores
def afterExpansion : ProgHOL 64 := .decCall (ofString "n") .one (ofString "sat_word") [localVar "size"] afterSize
def afterCost : ProgHOL 64 := MemoryExpansionCost.chargedProgram [.rfield 0 (localVar "x")] afterExpansion
def program : ProgHOL 64 := .decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1") [localVar "start", localVar "size"] afterCost

theorem body_shape : body = StackPop.pops ["start", "size"] program := by
  simp only [body, program, afterCost, MemoryExpansionCost.chargedProgram, afterExpansion, afterSize, stores, outputAddress,
    Guest.guestFn_op_revert, StackPop.pops, StackPop.shape, MemoryExtend.returnZero, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar, frameLoad, frameAddress]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "op_revert") = some ([], body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 523 (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_revert) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, Guest.guestFn_op_revert, shapeToHOL, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.body_shape
#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.original_code

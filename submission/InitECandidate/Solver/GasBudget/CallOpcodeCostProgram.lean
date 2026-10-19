import InitECandidate.Solver.GasBudget.CallOpcodeProgram
import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Prefix

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterMessage : ProgHOL 64 := match afterPops with | .dec _ _ _ rest => rest | _ => .skip
def afterZero : ProgHOL 64 := match afterMessage with | .decCall _ _ _ _ rest => rest | _ => .skip
def staticGuard : ProgHOL 64 := match afterZero with | .seq first _ => first | _ => .skip
def costProgram : ProgHOL 64 := match afterZero with | .seq _ rest => rest | _ => .skip
def afterCost : ProgHOL 64 := match costProgram with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterFee : ProgHOL 64 := match afterCost with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq _ (.dec _ _ _ (.seq _ (.decCall _ _ _ _ (.seq _ rest)))))) => rest
  | _ => .skip

set_option maxRecDepth 10000 in
theorem message_shape : afterPops = .dec (ofString "msg") .one (frameLoad 112#64) afterMessage := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]
set_option maxRecDepth 10000 in
theorem zero_shape : afterMessage = .decCall (ofString "vz") .one (ofString "u256_is_zero") [localVar "value"] afterZero := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]
set_option maxRecDepth 10000 in
theorem guard_shape : afterZero = .seq staticGuard costProgram := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]
set_option maxRecDepth 10000 in
theorem static_pure : Input.PureGuard staticGuard := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]
  exact .ite _ (.raise _ _) .skip
set_option maxRecDepth 10000 in
theorem cost_shape : costProgram = .decCall (ofString "x") MemoryExpansionCost2.pairShape (ofString "extend_memory_cost2")
    [localVar "in_start", localVar "in_size", localVar "out_start", localVar "out_size"] afterCost := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]
set_option maxRecDepth 10000 in
theorem first_fee_shape : afterCost = CallFirstFee.program [localVar "to"] afterFee := by
  simp only [afterFee, afterCost, costProgram, staticGuard, afterZero, afterMessage, afterPops, body,
    Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, frameLoad, frameAddress, localVar, MemoryExpansionCost2.pairShape,
    CallFirstFee.program, CallAccessFee.program, CallAccessFee.update, CallValueFee.withTransfer, CallValueFee.transferUpdate,
    CallValueFee.program, CallValueFee.afterFee, CallValueFee.feeExpression]

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.message_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.zero_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.guard_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.static_pure
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.cost_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.first_fee_shape

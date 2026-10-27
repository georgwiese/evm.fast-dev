import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.GasBudget.ArithmeticEffects
import InitECandidate.Solver.GasBudget.ArithmeticStackCall
import InitECandidate.Solver.GasBudget.DispatchProgram
import InitECandidate.Solver.GasBudget.StopNormal
import InitECandidate.Solver.GasBudget.JumpdestNormal

namespace InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

-- Literal positions in the unchanged source; this catalogue is not executable code.
def arithmeticIndex : ArithmeticEffects.Kind → Nat
  | .add_sat => 399
  | .bit_length64 => 71
  | .bswap64 => 18
  | .ceil_log2 => 31
  | .digits_len => 60
  | .digits_to_u256 => 59
  | .div64by32 => 57
  | .max => 27
  | .min => 26
  | .mul64x64 => 53
  | .nlz32 => 56
  | .sat_word => 398
  | .u256_add => 50
  | .u256_add_carry => 49
  | .u256_and => 46
  | .u256_eq => 39
  | .u256_fits_word => 35
  | .u256_from_word => 33
  | .u256_is_zero => 36
  | .u256_limb => 37
  | .u256_low => 34
  | .u256_lt => 40
  | .u256_neg => 52
  | .u256_not => 45
  | .u256_or => 47
  | .u256_shl => 75
  | .u256_shr => 76
  | .u256_slt => 42
  | .u256_sub => 51
  | .u256_xor => 48
  | .u256_abs => 66
  | .u256_bit => 38
  | .u256_bit_length => 72
  | .u256_byte => 79
  | .u256_cmp => 44
  | .u256_from_be => 80
  | .u256_gt => 41
  | .u256_mul => 54
  | .u256_mul_full => 55
  | .u256_sar => 77
  | .u256_sgt => 43
  | .u256_byte_length => 73
  | .u256_exp => 74
  | .u256_signextend => 78

theorem arithmetic_index (kind : ArithmeticEffects.Kind) :
    (functionsHOL Input.OriginalCode.program)[arithmeticIndex kind]? = some (kind.name, kind.signature) := by
  cases kind <;> rfl

theorem arithmetic (code) (installed : Input.OriginalCode.Installed code) : ArithmeticEffects.Environment code := by
  intro kind
  exact Input.OriginalCode.indexed code installed (arithmeticIndex kind) (kind.name, kind.signature) (arithmetic_index kind)

theorem stack_pop (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape) := by
  have found : (functionsHOL Input.OriginalCode.program)[411]? = some (originalEntry Guest.guestFn_stack_pop) := by rfl
  have checked := Input.OriginalCode.indexed code installed 411 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_stack_pop, StackPop.body, StackPop.shape, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem stack_push (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "stack_push") = some (StackPush.formals, StackPush.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[412]? = some (originalEntry Guest.guestFn_stack_push) := by rfl
  have checked := Input.OriginalCode.indexed code installed 412 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_stack_push, StackPush.body, StackPush.formals, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem charge_gas (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[406]? = some (originalEntry Guest.guestFn_charge_gas) := by rfl
  have checked := Input.OriginalCode.indexed code installed 406 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_charge_gas, RegularCharge.body, RegularCharge.formals, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem pc_add (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[426]? = some (originalEntry Guest.guestFn_pc_add) := by rfl
  have checked := Input.OriginalCode.indexed code installed 426 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_pc_add, PcAdd.body, PcAdd.formals, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem op_dispatch (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_dispatch") = some (OpcodeDispatch.formals, OpcodeDispatch.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[531]? = some (originalEntry Guest.guestFn_op_dispatch) := by rfl
  have checked := Input.OriginalCode.indexed code installed 531 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_dispatch, OpcodeDispatch.body, OpcodeDispatch.formals, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem op_stop (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_stop") = some ([], Stop.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[460]? = some (originalEntry Guest.guestFn_op_stop) := by rfl
  have checked := Input.OriginalCode.indexed code installed 460 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_stop, Stop.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem op_jumpdest (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_jumpdest") = some ([], Jumpdest.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[465]? = some (originalEntry Guest.guestFn_op_jumpdest) := by rfl
  have checked := Input.OriginalCode.indexed code installed 465 _ found
  simpa only [originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_jumpdest, Jumpdest.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

def opcodeIndex : ArithmeticStackOpcode.Kind → Nat
  | .op_add => 433
  | .op_mul => 434
  | .op_sub => 435
  | .op_signextend => 443
  | .op_shl => 455
  | .op_shr => 456
  | .op_sar => 457

theorem opcode_index (kind : ArithmeticStackOpcode.Kind) :
    (functionsHOL Input.OriginalCode.program)[opcodeIndex kind]? = some (kind.function, ([], kind.site.body, .one)) := by
  cases kind
  case op_add =>
    have found : (functionsHOL Input.OriginalCode.program)[433]? = some (originalEntry Guest.guestFn_op_add) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_add, shapeToHOL, List.map_nil] using found
  case op_mul =>
    have found : (functionsHOL Input.OriginalCode.program)[434]? = some (originalEntry Guest.guestFn_op_mul) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_mul, shapeToHOL, List.map_nil] using found
  case op_sub =>
    have found : (functionsHOL Input.OriginalCode.program)[435]? = some (originalEntry Guest.guestFn_op_sub) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_sub, shapeToHOL, List.map_nil] using found
  case op_signextend =>
    have found : (functionsHOL Input.OriginalCode.program)[443]? = some (originalEntry Guest.guestFn_op_signextend) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_signextend, shapeToHOL, List.map_nil] using found
  case op_shl =>
    have found : (functionsHOL Input.OriginalCode.program)[455]? = some (originalEntry Guest.guestFn_op_shl) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_shl, shapeToHOL, List.map_nil] using found
  case op_shr =>
    have found : (functionsHOL Input.OriginalCode.program)[456]? = some (originalEntry Guest.guestFn_op_shr) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_shr, shapeToHOL, List.map_nil] using found
  case op_sar =>
    have found : (functionsHOL Input.OriginalCode.program)[457]? = some (originalEntry Guest.guestFn_op_sar) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_op_sar, shapeToHOL, List.map_nil] using found

theorem arithmetic_opcode (code) (installed : Input.OriginalCode.Installed code) (kind : ArithmeticStackOpcode.Kind) :
    code.lookup kind.function = some ([], kind.site.body, .one) :=
  Input.OriginalCode.indexed code installed (opcodeIndex kind) _ (opcode_index kind)

end InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic_index
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.opcode_index
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic_opcode
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.stack_pop
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.stack_push
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.charge_gas
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.pc_add
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.op_dispatch
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.op_stop
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.op_jumpdest

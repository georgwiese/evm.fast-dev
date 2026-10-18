import InitECandidate.Solver.GasBudget.ChargeWithMemoryPrefix
import InitECandidate.Solver.GasBudget.ChargeWithMemoryLookup
import InitECandidate.Solver.Input.ExecutionTail
import InitECandidate.Solver.Input.ExceptionControl
import InitECandidate.Solver.GasBudget.StackPopsException

namespace InitECandidate.Solver.GasBudget.MemoryOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | mload | mstore | mstore8

def Kind.original : Kind → Decl (BitVec 64)
  | .mload => Guest.guestFn_op_mload
  | .mstore => Guest.guestFn_op_mstore
  | .mstore8 => Guest.guestFn_op_mstore8
def Kind.label : Kind → String
  | .mload => "op_mload" | .mstore => "op_mstore" | .mstore8 => "op_mstore8"
def Kind.name (kind : Kind) : MlS := ofString kind.label
def Kind.body (kind : Kind) : ProgHOL 64 := match kind.original with | .function fn => progToHOL fn.body | _ => .skip
def Kind.names : Kind → List String
  | .mload => ["start"] | .mstore | .mstore8 => ["start", "value"]
def Kind.size : Kind → BitVec 64
  | .mload | .mstore => 32#64 | .mstore8 => 1#64
def Kind.arguments (kind : Kind) : List (ExpHOL 64) :=
  [.const 3#64, localVar "start", .rstruct [.const kind.size, .const 0#64, .const 0#64, .const 0#64]]
def Kind.suffix (kind : Kind) : ProgHOL 64 := match OpcodeChargeSites.stripPops kind.names.length kind.body with
  | .seq _ rest => rest | _ => .skip
def Kind.index : Kind → Nat
  | .mload => 468 | .mstore => 466 | .mstore8 => 467

theorem body_shape (kind : Kind) : kind.body = StackPop.pops kind.names
    (.seq (.call (some (none, none)) (ofString "charge_with_memory") kind.arguments) kind.suffix) := by
  cases kind <;> simp only [Kind.body, Kind.original, Kind.names, Kind.arguments, Kind.size, Kind.suffix,
    Guest.guestFn_op_mload, Guest.guestFn_op_mstore, Guest.guestFn_op_mstore8, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, Option.map_none, StackPop.pops, StackPop.shape,
    OpcodeChargeSites.stripPops, localVar]

set_option maxRecDepth 100000 in
theorem original_index (kind : Kind) : (functionsHOL Input.OriginalCode.program)[kind.index]? =
    some (OriginalCodeEnvironment.originalEntry kind.original) := by cases kind <;> rfl

theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup kind.name = some ([], kind.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed kind.index _ (original_index kind)
  cases kind <;> simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Kind.original,
    Kind.name, Kind.label, Kind.body, Guest.guestFn_op_mload, Guest.guestFn_op_mstore, Guest.guestFn_op_mstore8,
    shapeToHOL, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.MemoryOpcode

#print axioms InitECandidate.Solver.GasBudget.MemoryOpcode.body_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryOpcode.original_index
#print axioms InitECandidate.Solver.GasBudget.MemoryOpcode.original_code

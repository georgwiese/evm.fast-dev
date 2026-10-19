import InitECandidate.Solver.GasBudget.ChargeWithMemorySetup
import InitECandidate.Solver.GasBudget.WordsOfCallPrefix

namespace InitECandidate.Solver.GasBudget.CopyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | keccak | returndata
def Kind.original : Kind → Decl (BitVec 64)
  | .keccak => Guest.guestFn_op_keccak | .returndata => Guest.guestFn_op_returndatacopy
def Kind.label : Kind → String | .keccak => "op_keccak" | .returndata => "op_returndatacopy"
def Kind.name (kind : Kind) : MlS := ofString kind.label
def Kind.body (kind : Kind) : ProgHOL 64 := match kind.original with | .function fn => progToHOL fn.body | _ => .skip
def Kind.names : Kind → List String | .keccak => ["start", "size"] | .returndata => ["mstart", "rstart", "size"]
def Kind.start : Kind → String | .keccak => "start" | .returndata => "mstart"
def Kind.base : Kind → Nat | .keccak => 30 | .returndata => 3
def Kind.slope : Kind → Nat | .keccak => 6 | .returndata => 3
def Kind.suffix (kind : Kind) : ProgHOL 64 := match OpcodeChargeSites.stripPops kind.names.length kind.body with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ rest)))) => rest
  | _ => .skip
def Kind.afterFee (kind : Kind) : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "charge_gas") [localVar "cost"]) kind.suffix
def Kind.fee (kind : Kind) : ExpHOL 64 := .op .add [.const (BitVec.ofNat 64 kind.base), .panop .mul [.const (BitVec.ofNat 64 kind.slope), localVar "w"]]
def Kind.afterCost (kind : Kind) : ProgHOL 64 := .decCall (ofString "cost") .one (ofString "add_sat") [kind.fee, .rfield 0 (localVar "x")] kind.afterFee
def Kind.afterWords (kind : Kind) : ProgHOL 64 := .decCall (ofString "x") ChargeWithMemory.pair (ofString "extend_memory_cost1")
  [localVar kind.start, localVar "size"] kind.afterCost
def Kind.afterSat (kind : Kind) : ProgHOL 64 := .decCall (ofString "w") .one (ofString "words_of") [localVar "n"] kind.afterWords
def Kind.program (kind : Kind) : ProgHOL 64 := .decCall (ofString "n") .one (ofString "sat_word") [localVar "size"] kind.afterSat
def Kind.index : Kind → Nat | .keccak => 459 | .returndata => 505

theorem body_shape (kind : Kind) : kind.body = StackPop.pops kind.names kind.program := by
  cases kind <;> simp only [Kind.body, Kind.original, Kind.names, Kind.program, Kind.afterSat, Kind.afterWords, Kind.afterCost,
    Kind.afterFee, Kind.fee, Kind.base, Kind.slope, Kind.start, Kind.suffix, Guest.guestFn_op_keccak, Guest.guestFn_op_returndatacopy,
    OpcodeChargeSites.stripPops, StackPop.pops, StackPop.shape, ChargeWithMemory.pair, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, Option.map_none, localVar]

set_option maxRecDepth 100000 in
theorem original_index (kind : Kind) : (functionsHOL Input.OriginalCode.program)[kind.index]? =
    some (OriginalCodeEnvironment.originalEntry kind.original) := by cases kind <;> rfl

theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup kind.name = some ([], kind.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed kind.index _ (original_index kind)
  cases kind <;> simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Kind.original, Kind.name, Kind.label,
    Kind.body, Guest.guestFn_op_keccak, Guest.guestFn_op_returndatacopy, shapeToHOL, List.map_nil] using checked

theorem charge_choice (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (amount : BitVec 64)
    (cell : source.locals.lookup (ofString "cost") = some (.val (.word amount))) :
    evaluateHOLFiniteState source kind.afterFee = evaluateHOLFiniteState source (OpcodeChargePrefix.program [] amount kind.suffix) := by
  apply Input.ArgumentValues.ignored_sequence_eq
  simp [Kind.afterFee, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell]

end InitECandidate.Solver.GasBudget.CopyCost

#print axioms InitECandidate.Solver.GasBudget.CopyCost.body_shape
#print axioms InitECandidate.Solver.GasBudget.CopyCost.original_index
#print axioms InitECandidate.Solver.GasBudget.CopyCost.original_code

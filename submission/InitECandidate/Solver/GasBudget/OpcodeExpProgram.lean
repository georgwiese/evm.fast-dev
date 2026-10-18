import InitECandidate.Solver.GasBudget.ByteLengthCallPrefix
import InitECandidate.Solver.GasBudget.OpcodeChargeSites
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.OpcodeExp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_op_exp with | .function fn => progToHOL fn.body | _ => .skip
def names : List String := ["base", "exponent"]
def afterPops : ProgHOL 64 := OpcodeChargeSites.stripPops 2 body
def suffix : ProgHOL 64 := match afterPops with
  | .decCall _ _ _ _ (.seq _ rest) => rest
  | _ => .skip
def fee (bytes : Nat) : Nat := 10 + 50 * bytes
def amount (bytes : Nat) : BitVec 64 := BitVec.ofNat 64 (fee bytes)
def gasExpression : ExpHOL 64 := .op .add [.const 10#64, .panop .mul [.const 50#64, localVar "nb"]]
def afterBytes : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "charge_gas") [gasExpression]) suffix

theorem body_shape : body = StackPop.pops names
    (.decCall (ofString "nb") .one (ofString "u256_byte_length") [localVar "exponent"] afterBytes) := by
  simp only [body, Guest.guestFn_op_exp, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    names, StackPop.pops, StackPop.shape, afterBytes, gasExpression, suffix, afterPops,
    OpcodeChargeSites.stripPops, localVar]

theorem fee_word (bytes : Nat) (small : bytes ≤ 32) : (amount bytes).toNat = fee bytes := by
  rw [amount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold fee
  omega

theorem fee_positive (bytes : Nat) : 0 < fee bytes := by unfold fee; omega

theorem expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : Nat)
    (cell : source.locals.lookup (ofString "nb") = some (.val (.word (BitVec.ofNat 64 bytes)))) :
    eval source gasExpression = some (.val (.word (amount bytes))) := by
  simp [eval, gasExpression, evalHOLExact, evalListHOLExact, localVar, cell, toExact,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, amount, fee, BitVec.ofNat_add, BitVec.ofNat_mul]

/-- Literalize only the argument of the real charge call at its actual
reached state. The original AST/continuation is otherwise unchanged, and
the equation covers every evaluator outcome. -/
theorem charge_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : Nat)
    (cell : source.locals.lookup (ofString "nb") = some (.val (.word (BitVec.ofNat 64 bytes)))) :
    evaluateHOLFiniteState source afterBytes = evaluateHOLFiniteState source (OpcodeChargePrefix.program [] (amount bytes) suffix) := by
  have read := expression_read source bytes cell
  simp only [eval] at read
  have arguments : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [gasExpression] =
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const (amount bytes)] := by
    simp only [evalListHOLFinite, evalListHOLExact, read, evalHOLExact]
  have callEq : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") [gasExpression]) =
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") [.const (amount bytes)]) := by
    rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, arguments]
  simp only [afterBytes, OpcodeChargePrefix.program, StackPop.pops, evaluateHOLFiniteState_seq_line780]
  rw [callEq]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_exp") = some ([], body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[442]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_exp) := by rfl
  have checked := Input.OriginalCode.indexed code installed 442 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_exp,
    body, shapeToHOL, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.OpcodeExp

#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.fee_word
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.expression_read
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.charge_choice
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.original_code

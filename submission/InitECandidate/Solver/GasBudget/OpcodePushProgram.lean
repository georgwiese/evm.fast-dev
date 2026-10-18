import InitECandidate.Solver.GasBudget.OpcodeChargeException
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.OpcodePush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_op_push with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "nbytes", .one)]
def test : ExpHOL 64 := .cmp .equal (localVar "nbytes") (.const 0#64)
def charge (amount : BitVec 64) : ProgHOL 64 := .call (some (none, none)) (ofString "charge_gas") [.const amount]
def choice : ProgHOL 64 := .ite test (charge 2#64) (charge 3#64)
def suffix : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def amount (bytes : BitVec 64) : BitVec 64 := if bytes = 0#64 then 2#64 else 3#64
def fee (bytes : BitVec 64) : Nat := if bytes = 0#64 then 2 else 3

theorem body_shape : body = .seq choice suffix := by
  simp only [body, Guest.guestFn_op_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, choice, test, charge, suffix, localVar]

theorem amount_value (bytes : BitVec 64) : (amount bytes).toNat = fee bytes := by
  by_cases zero : bytes = 0#64 <;> simp [amount, fee, zero]

theorem fee_positive (bytes : BitVec 64) : 0 < fee bytes := by unfold fee; split <;> decide
theorem fee_bounded (bytes : BitVec 64) : fee bytes ≤ 3 := by unfold fee; split <;> decide

/-- Exact original branch choice before any mutation. PUSH0 charges2 and
the other branch charges3; the whole original suffix remains unchanged. -/
theorem body_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : BitVec 64)
    (bytesLocal : source.locals.lookup (ofString "nbytes") = some (.val (.word bytes))) :
    evaluateHOLFiniteState source body = evaluateHOLFiniteState source (OpcodeChargePrefix.program [] (amount bytes) suffix) := by
  have first : evaluateHOLFiniteState source choice = evaluateHOLFiniteState source (charge (amount bytes)) := by
    by_cases zero : bytes = 0#64
    · have testRead : eval source test = some (.val (.word 1#64)) := by
        simp [eval, test, evalHOLExact, toExact, localVar, bytesLocal, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp only [eval] at testRead
      rw [choice, evaluateHOLFiniteState_ite, testRead]
      change evaluateHOLFiniteState source (charge 2#64) = _
      rw [amount, if_pos zero]
    · have testRead : eval source test = some (.val (.word 0#64)) := by
        simp [eval, test, evalHOLExact, toExact, localVar, bytesLocal, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp only [eval] at testRead
      rw [choice, evaluateHOLFiniteState_ite, testRead]
      change evaluateHOLFiniteState source (charge 3#64) = _
      rw [amount, if_neg zero]
  rw [body_shape]
  change evaluateHOLFiniteState source (.seq choice suffix) = evaluateHOLFiniteState source (.seq (charge (amount bytes)) suffix)
  simp only [evaluateHOLFiniteState_seq_line780, first]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_push") = some (formals, body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[472]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_push) := by rfl
  have checked := Input.OriginalCode.indexed code installed 472 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_push,
    formals, body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.OpcodePush

#print axioms InitECandidate.Solver.GasBudget.OpcodePush.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.body_choice
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.amount_value
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.fee_positive
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.original_code

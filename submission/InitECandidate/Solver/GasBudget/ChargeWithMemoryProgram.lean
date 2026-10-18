import InitECandidate.Solver.GasBudget.MemoryCostNoException
import InitECandidate.Solver.GasBudget.SaturatingAddPrefix
import InitECandidate.Solver.GasBudget.OpcodeChargePrefix
import InitECandidate.Solver.Input.ArgumentValues

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_charge_with_memory with | .function fn => progToHOL fn.body | _ => .skip
def pair : ShapeHOL := .comb [.one, .one]
def suffix : ProgHOL 64 := match body with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ rest)) => rest
  | _ => .skip
def afterTotal : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "charge_gas") [localVar "total"]) suffix
def afterCost : ProgHOL 64 := .decCall (ofString "total") .one (ofString "add_sat")
  [localVar "base", .rfield 0 (localVar "x")] afterTotal

theorem body_shape : body = .decCall (ofString "x") pair (ofString "extend_memory_cost1")
    [localVar "start", localVar "size"] afterCost := by
  simp only [body, Guest.guestFn_charge_with_memory, suffix, afterCost, afterTotal, pair,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar]

theorem charge_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (amount : BitVec 64)
    (cell : source.locals.lookup (ofString "total") = some (.val (.word amount))) :
    evaluateHOLFiniteState source afterTotal = evaluateHOLFiniteState source (OpcodeChargePrefix.program [] amount suffix) := by
  apply Input.ArgumentValues.ignored_sequence_eq
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell]

theorem add_signature : ArithmeticEffects.Kind.add_sat.signature = (AddExact.formals, AddExact.body, .one) := by
  simp only [ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, AddExact.formals, AddExact.body,
    Guest.guestFn_add_sat, shapeToHOL, List.map_cons, List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "charge_with_memory") = some ([(ofString "base", .one),
      (ofString "start", StackPop.shape), (ofString "size", StackPop.shape)], body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[419]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_charge_with_memory) := by rfl
  have checked := Input.OriginalCode.indexed code installed 419 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_charge_with_memory,
    body, StackPop.shape, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.body_shape
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.charge_choice
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.add_signature
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.original_code

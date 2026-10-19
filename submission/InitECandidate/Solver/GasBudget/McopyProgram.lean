import InitECandidate.Solver.GasBudget.CopyCostProgram
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2AnyPrefix
import InitECandidate.Solver.GasBudget.MemoryExpansionCostPopView

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_op_mcopy with | .function fn => progToHOL fn.body | _ => .skip
def names : List String := ["dst", "src", "len"]
def suffix : ProgHOL 64 := match OpcodeChargeSites.stripPops 3 body with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ rest)))) => rest
  | _ => .skip
def afterFee : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "charge_gas") [localVar "cost"]) suffix
def fee : ExpHOL 64 := .op .add [.const 3#64, .panop .mul [.const 3#64, localVar "w"]]
def afterCost : ProgHOL 64 := .decCall (ofString "cost") .one (ofString "add_sat") [fee, .rfield 0 (localVar "x")] afterFee
def afterWords : ProgHOL 64 := .decCall (ofString "x") MemoryExpansionCost2.pairShape (ofString "extend_memory_cost2")
  [localVar "src", localVar "len", localVar "dst", localVar "len"] afterCost
def afterSat : ProgHOL 64 := .decCall (ofString "w") .one (ofString "words_of") [localVar "n"] afterWords
def program : ProgHOL 64 := .decCall (ofString "n") .one (ofString "sat_word") [localVar "len"] afterSat

theorem body_shape : body = StackPop.pops names program := by
  simp only [body, names, program, afterSat, afterWords, afterCost, afterFee, fee, suffix, Guest.guestFn_op_mcopy,
    OpcodeChargeSites.stripPops, StackPop.pops, StackPop.shape, MemoryExpansionCost2.pairShape, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]

set_option maxRecDepth 100000 in
theorem original_index : (functionsHOL Input.OriginalCode.program)[470]? =
    some (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_mcopy) := by rfl

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_mcopy") = some ([], body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 470 _ original_index
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, Guest.guestFn_op_mcopy,
    shapeToHOL, List.map_nil] using checked

theorem charge_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (amount : BitVec 64)
    (cell : source.locals.lookup (ofString "cost") = some (.val (.word amount))) :
    evaluateHOLFiniteState source afterFee = evaluateHOLFiniteState source (OpcodeChargePrefix.program [] amount suffix) := by
  apply Input.ArgumentValues.ignored_sequence_eq
  simp [afterFee, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell]

theorem fee_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "w") = some (.val (.word word))) :
    eval source fee = some (.val (.word (3#64 + 3#64 * word))) := by
  simp [fee, eval, evalHOLExact, evalListHOLExact, toExact, localVar, cell, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.body_shape
#print axioms InitECandidate.Solver.GasBudget.Mcopy.original_index
#print axioms InitECandidate.Solver.GasBudget.Mcopy.original_code
#print axioms InitECandidate.Solver.GasBudget.Mcopy.charge_choice
#print axioms InitECandidate.Solver.GasBudget.Mcopy.fee_read

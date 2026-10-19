import InitECandidate.Solver.Mpt.AccountImage
import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.Input.RlpWrite.U256Load
import InitECandidate.Solver.MutableTable.MemeqSmallScopedCall

namespace InitECandidate.Solver.Mpt.AccountIsEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_acct_is_empty with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "a", .one)]
def field (offset : BitVec 64) (shape : ShapeHOL := .one) : ExpHOL 64 := .load shape (.op .add [localVar "a", .const offset])
def balanceTail : ProgHOL 64 := .decCall (ofString "z") .one (ofString "u256_is_zero")
  [field 8#64 Input.RlpWrite.U256Value.tupleShape] (.return (localVar "z"))
def afterCompare : ProgHOL 64 := .seq
  (.ite (.cmp .equal (localVar "eq") (.const 0#64)) (.return (.const 0#64)) .skip) balanceTail
def compare : ProgHOL 64 := .decCall (ofString "eq") .one (ofString "memeq")
  [field 48#64, .var .global (ofString "empty_code_hash"), .const 32#64] afterCompare

theorem body_shape : body = .seq
    (.ite (.cmp .notEqual (field 0#64) (.const 0#64)) (.return (.const 0#64)) .skip) compare := by
  simp only [body,field,compare,afterCompare,balanceTail,Input.RlpWrite.U256Value.tupleShape,localVar,
    Guest.guestFn_acct_is_empty,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "acct_is_empty") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 352 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_acct_is_empty) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_acct_is_empty,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountIsEmpty

#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.original_code

import InitECandidate.Solver.GasBudget.U256Arithmetic
import InitECandidate.Solver.GasBudget.U256Zero
import InitECandidate.Solver.Input.MainBnAccelProgram

namespace InitECandidate.Solver.Input.FqNeg
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
abbrev Words := RlpWrite.U256Value.Words

def body : ProgHOL 64 := match Guest.guestFn_fq_neg with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "a",RlpWrite.U256Value.tupleShape)]
def modulusExpression : ExpHOL 64 := .rstruct [.const 4332616871279656263#64,.const 10917124144477883021#64,.const 13281191951274694749#64,.const 3486998266802970665#64]
def zeroReturn : ProgHOL 64 := .return (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
def guard : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "z")) (.const 1#64)) zeroReturn .skip
def subtraction : ProgHOL 64 := .call none (ofString "u256_sub") [modulusExpression,.var .local (ofString "a")]
def afterZero : ProgHOL 64 := .seq guard subtraction

theorem body_shape : body = .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "a")] afterZero := by
  simp only [body,afterZero,guard,subtraction,modulusExpression,zeroReturn,Guest.guestFn_fq_neg,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "fq_neg") = some (formals,body,RlpWrite.U256Value.tupleShape) := by
  have checked := OriginalCode.indexed code installed 601 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_fq_neg) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,RlpWrite.U256Value.tupleShape,Guest.guestFn_fq_neg,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem zero_original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "u256_is_zero") = some (GasBudget.U256Zero.formals,GasBudget.U256Zero.body,.one) := by
  have checked := OriginalCode.indexed code installed 36 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_is_zero) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,GasBudget.U256Zero.body,GasBudget.U256Zero.formals,RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_is_zero,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.FqNeg

#print axioms InitECandidate.Solver.Input.FqNeg.body_shape
#print axioms InitECandidate.Solver.Input.FqNeg.original_code
#print axioms InitECandidate.Solver.Input.FqNeg.zero_original_code

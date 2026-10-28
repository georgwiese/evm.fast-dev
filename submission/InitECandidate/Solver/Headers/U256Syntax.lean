import InitECandidate.Solver.Headers.FieldSyntax
import InitECandidate.Solver.Input.WordTupleFour

namespace InitECandidate.Solver.Headers.U256Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_hdr_u256_field with | .function fn=>progToHOL fn.body | _=>.skip
def afterField : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterGuard : ProgHOL 64 := match afterField with | .seq _ rest=>rest | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "arr",localVar "i",localVar "maxb"]
def convertArguments : List (ExpHOL 64) := [.rfield 0 (localVar "f"),.rfield 1 (localVar "f")]
def guardTest : ExpHOL 64 := .cmp .lower (.const 32#64) (.rfield 1 (localVar "f"))

theorem body_shape : body=.decCall (ofString "f") (.comb [.one,.one]) (ofString "hdr_uint_field") arguments afterField := by
  simp only [body,afterField,arguments,localVar,Guest.Software.guestFn_hdr_u256_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem field_shape : afterField=.seq (.ite guardTest (.raise (ofString "HdrErr") (.const 5#64)) .skip) afterGuard := by
  simp only [afterField,afterGuard,body,guardTest,localVar,Guest.Software.guestFn_hdr_u256_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem after_guard_shape : afterGuard=.decCall (ofString "v") Input.RlpWrite.U256Value.tupleShape (ofString "u256_from_be") convertArguments (.return (localVar "v")) := by
  simp only [afterGuard,afterField,body,convertArguments,Input.RlpWrite.U256Value.tupleShape,localVar,
    Guest.Software.guestFn_hdr_u256_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
/-- Literal original four-word integer-field decoder205. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "hdr_u256_field")=some (Field.Kind.uint.formals,body,Input.RlpWrite.U256Value.tupleShape) := by
  have checked := Input.OriginalCode.indexed code installed 205 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_hdr_u256_field) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Field.Kind.formals,body,Input.RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_hdr_u256_field,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Headers.U256Field

#print axioms InitECandidate.Solver.Headers.U256Field.body_shape
#print axioms InitECandidate.Solver.Headers.U256Field.field_shape
#print axioms InitECandidate.Solver.Headers.U256Field.after_guard_shape
#print axioms InitECandidate.Solver.Headers.U256Field.original_code

import InitECandidate.Solver.Rlp.ItemCallFrame
import InitECandidate.Solver.Rlp.DecodeCost

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | uint | bytes | raw
  deriving DecidableEq

def Kind.name : Kind→MlS
  | .uint=>ofString "hdr_uint_field" | .bytes=>ofString "hdr_bytes_field" | .raw=>ofString "hdr_raw_field"
def Kind.declaration : Kind→Decl (BitVec 64)
  | .uint=>Guest.guestFn_hdr_uint_field | .bytes=>Guest.guestFn_hdr_bytes_field | .raw=>Guest.guestFn_hdr_raw_field
def Kind.body (kind : Kind) : ProgHOL 64 := match kind.declaration with | .function fn=>progToHOL fn.body | _=>.skip
def Kind.formals : Kind→List (MlS×ShapeHOL)
  | .uint=>[(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)]
  | .bytes=>[(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)]
  | .raw=>[(ofString "arr",.one),(ofString "i",.one)]
def Kind.resultShape : Kind→ShapeHOL
  | .bytes=>.one | _=>.comb [.one,.one]
def Kind.afterItem (kind : Kind) : ProgHOL 64 := match kind.body with | .decCall _ _ _ _ rest=>rest | _=>.skip

def rowExpression : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]
def rowLengthExpression : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]
def arguments : List (ExpHOL 64) := [.load .one rowExpression,.load .one rowLengthExpression]

theorem body_shape (kind : Kind) : kind.body=.decCall (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") arguments kind.afterItem := by
  cases kind <;> simp only [Kind.body,Kind.declaration,Kind.afterItem,arguments,rowExpression,rowLengthExpression,Rlp.Item.resultShape,localVar,
    Guest.guestFn_hdr_uint_field,Guest.guestFn_hdr_bytes_field,Guest.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
/-- Three unchanged original scalar/byte header field helpers. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) (kind : Kind) :
    code.lookup kind.name=some (kind.formals,kind.body,kind.resultShape) := by
  cases kind
  · have checked := Input.OriginalCode.indexed code installed 205 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_hdr_uint_field) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Kind.name,Kind.formals,Kind.body,Kind.declaration,Kind.resultShape,
      Guest.guestFn_hdr_uint_field,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked := Input.OriginalCode.indexed code installed 208 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_hdr_bytes_field) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Kind.name,Kind.formals,Kind.body,Kind.declaration,Kind.resultShape,
      Guest.guestFn_hdr_bytes_field,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked := Input.OriginalCode.indexed code installed 209 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_hdr_raw_field) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Kind.name,Kind.formals,Kind.body,Kind.declaration,Kind.resultShape,
      Guest.guestFn_hdr_raw_field,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.body_shape
#print axioms InitECandidate.Solver.Headers.Field.original_code

import InitECandidate.Solver.Headers.FieldCallSyntax
import InitECandidate.Solver.Headers.WordProgram
import InitECandidate.Solver.Headers.U256Syntax
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Headers.Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where | uint | bytes | raw | word | u256
  deriving DecidableEq

def Kind.name : Kind→MlS
  | .uint=>Field.Kind.uint.name | .bytes=>Field.Kind.bytes.name | .raw=>Field.Kind.raw.name
  | .word=>ofString "hdr_word_field" | .u256=>ofString "hdr_u256_field"
def Kind.body : Kind→ProgHOL 64
  | .uint=>Field.Kind.uint.body | .bytes=>Field.Kind.bytes.body | .raw=>Field.Kind.raw.body
  | .word=>WordField.body | .u256=>U256Field.body
def Kind.formals : Kind→List (MlS×ShapeHOL)
  | .uint | .u256=>Field.Kind.uint.formals | .bytes=>Field.Kind.bytes.formals | _=>Field.Kind.raw.formals
def Kind.resultShape : Kind→ShapeHOL
  | .bytes | .word=>.one | .u256=>Input.RlpWrite.U256Value.tupleShape | _=>.comb [.one,.one]
def Kind.ternary : Kind→Bool | .raw | .word=>false | _=>true
def Kind.controlName : Kind→MlS | .bytes=>ofString "width" | .uint | .u256=>ofString "maxb" | _=>ofString ""
def Kind.values (kind : Kind) (array index control : BitVec 64) : List (ValueHOL 64) :=
  if kind.ternary then [.val (.word array),.val (.word index),.val (.word control)] else [.val (.word array),.val (.word index)]
/-- The common field interface links only the five unchanged original
functions203..207; it introduces no alternate executable implementation. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) (kind : Kind) :
    code.lookup kind.name=some (kind.formals,kind.body,kind.resultShape) := by
  cases kind
  · exact Field.original_code code installed .uint
  · exact Field.original_code code installed .bytes
  · exact Field.original_code code installed .raw
  · exact WordField.original_code code installed
  · exact U256Field.original_code code installed

/-- Each real scalar field ABI retains its actual array/index/control
bindings. Binary helpers have no control-parameter premise. -/
theorem environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (kind : Kind) (array index control : BitVec 64)
    (known : table kind.name=some (kind.formals,kind.body,kind.resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table kind.name (kind.values array index control)=some (kind.body,callee,kind.resultShape) ∧
      callee.lookup (ofString "arr")=some (.val (.word array)) ∧ callee.lookup (ofString "i")=some (.val (.word index)) ∧
      (kind.ternary=true → callee.lookup kind.controlName=some (.val (.word control))) := by
  cases kind
  · obtain ⟨callee,called,a,i,c⟩ := Field.environment table .uint array index control known
    exact ⟨callee,called,a,i,fun _=>c (by decide)⟩
  · obtain ⟨callee,called,a,i,c⟩ := Field.environment table .bytes array index control known
    exact ⟨callee,called,a,i,fun _=>c (by decide)⟩
  · obtain ⟨callee,called,a,i,c⟩ := Field.environment table .raw array index control known
    exact ⟨callee,called,a,i,by intro impossible; cases impossible⟩
  · obtain ⟨callee,called,a,i⟩ := Input.word_pair_environment table (ofString "hdr_word_field") (ofString "arr") (ofString "i") WordField.body .one array index (by decide) known
    exact ⟨callee,called,a,i,by intro impossible; cases impossible⟩
  · obtain ⟨callee,called,a,i,c⟩ := Input.word_triple_environment table (ofString "hdr_u256_field") (ofString "arr") (ofString "i") (ofString "maxb")
      U256Field.body Input.RlpWrite.U256Value.tupleShape array index control (by decide) (by decide) (by decide) known
    exact ⟨callee,called,a,i,fun _=>c⟩

end InitECandidate.Solver.Headers.Helper

#print axioms InitECandidate.Solver.Headers.Helper.original_code
#print axioms InitECandidate.Solver.Headers.Helper.environment

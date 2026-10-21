import InitECandidate.Solver.Rlp.DecodeCallFrame
import InitECandidate.Solver.Rlp.SlicesCallNormal
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_decode_header with | .function fn=>progToHOL fn.body | _=>.skip
def afterTop : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterKind : ProgHOL 64 := match afterTop with | .seq _ rest=>rest | _=>.skip
def afterList : ProgHOL 64 := match afterKind with | .decCall _ _ _ _ rest=>rest | _=>.skip
def topArguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def listArguments : List (ExpHOL 64) := [.rfield 1 (localVar "top"),.rfield 2 (localVar "top")]
def kindGuard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))
  (.raise (ofString "HdrErr") (.const 10#64)) .skip

theorem body_shape : body=.decCall (ofString "top") Rlp.Item.resultShape (ofString "rlp_decode_fully") topArguments afterTop := by
  simp only [body,afterTop,topArguments,Rlp.Item.resultShape,localVar,Guest.guestFn_decode_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem after_top_shape : afterTop=.seq kindGuard afterKind ∧
    afterKind=.decCall (ofString "lst") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") listArguments afterList := by
  simp only [afterTop,afterKind,afterList,body,kindGuard,listArguments,Rlp.Slices.resultShape,localVar,
    Guest.guestFn_decode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  trivial

set_option maxRecDepth 100000 in
/-- The unchanged original header decoder at its authoritative code index. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "decode_header")=some (Rlp.Header.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 210 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_decode_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Rlp.Header.formals,
    Guest.guestFn_decode_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.body_shape
#print axioms InitECandidate.Solver.Headers.Decode.after_top_shape
#print axioms InitECandidate.Solver.Headers.Decode.original_code

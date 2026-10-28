import InitECandidate.Solver.Rlp.ItemSyntax

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_decode_fully with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def afterItem : ProgHOL 64 := .seq
  (.ite (.cmp .notEqual (.rfield 3 (localVar "it")) (localVar "len")) (Header.fail 6#64) .skip) (.return (localVar "it"))

theorem body_shape : body=.decCall (ofString "it") Item.resultShape (ofString "rlp_item") arguments afterItem := by
  simp only [body,arguments,afterItem,Item.resultShape,Header.fail,localVar,Guest.Software.guestFn_rlp_decode_fully,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_decode_fully")=some (Header.formals,body,Item.resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 96 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_decode_fully) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,Item.resultShape,
    Guest.Software.guestFn_rlp_decode_fully,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.body_shape
#print axioms InitECandidate.Solver.Rlp.Decode.original_code

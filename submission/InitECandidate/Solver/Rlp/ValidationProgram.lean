import InitECandidate.Solver.Rlp.HeaderCallNormal
import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn__rlp_validate_items_body with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "len",.one)]
def afterSetup : ProgHOL 64 := match body with | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ rest))) => rest | _ => .skip
def loop : ProgHOL 64 := match afterSetup with | .seq first _ => first | _ => .skip
def loopBody : ProgHOL 64 := match loop with | .while _ rest => rest | _ => .skip
def condition : ExpHOL 64 := .cmp .notEqual (localVar "go") (.const 0#64)
def stop : ProgHOL 64 := .assign .local (ofString "go") (.const 0#64)
def pop : ProgHOL 64 := .seq (.assign .local (ofString "pos") (.load .one (addConst (localVar "top") 0#64)))
  (.seq (.assign .local (ofString "end") (.load .one (addConst (localVar "top") 8#64)))
    (.assign .local (ofString "top") (.load .one (addConst (localVar "top") 16#64))))
def move : ProgHOL 64 := .assign .local (ofString "pos") (localVar "after")
def pushMoves : ProgHOL 64 := .seq (.assign .local (ofString "top") (localVar "rec"))
  (.seq (.assign .local (ofString "pos") (localVar "payload")) (.assign .local (ofString "end") (localVar "after")))
def pushStores : ProgHOL 64 := .seq (.store (localVar "rec") (localVar "after"))
  (.seq (.store (addConst (localVar "rec") 8#64) (localVar "end"))
    (.seq (.store (addConst (localVar "rec") 16#64) (localVar "top")) pushMoves))
def push : ProgHOL 64 := .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24#64] pushStores
def choose : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 2 (localVar "h")) (.const 0#64)) push move
def afterHeader : ProgHOL 64 := .dec (ofString "payload") .one (.op .add [localVar "pos",.rfield 0 (localVar "h")])
  (.dec (ofString "after") .one (.op .add [localVar "payload",.rfield 1 (localVar "h")]) choose)
def headerArguments : List (ExpHOL 64) := [localVar "pos",.op .sub [localVar "end",localVar "pos"]]
def parse : ProgHOL 64 := .decCall (ofString "h") Header.resultShape (ofString "rlp_item_header") headerArguments afterHeader
def atEnd : ProgHOL 64 := .ite (.cmp .equal (localVar "top") (.const 0#64)) stop pop

set_option maxRecDepth 10000
theorem body_shape : body=.dec (ofString "top") .one (.const 0#64)
    (.dec (ofString "pos") .one (localVar "p")
      (.dec (ofString "end") .one (.op .add [localVar "p",localVar "len"])
        (.dec (ofString "go") .one (.const 1#64) (.seq loop (.return (.const 0#64)))))) := by
  simp only [body,loop,afterSetup,Guest.guestFn__rlp_validate_items_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,afterSetup,body,loopBody,condition,Guest.guestFn__rlp_validate_items_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
theorem loop_body_shape : loopBody=.ite (.cmp .equal (localVar "pos") (localVar "end")) atEnd parse := by
  simp only [loopBody,loop,afterSetup,body,atEnd,stop,pop,parse,headerArguments,afterHeader,choose,push,pushStores,pushMoves,move,
    Header.resultShape,localVar,addConst,
    Guest.guestFn__rlp_validate_items_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_rlp_validate_items_body")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 98 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__rlp_validate_items_body) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.guestFn__rlp_validate_items_body,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.body_shape
#print axioms InitECandidate.Solver.Rlp.Validation.loop_shape
#print axioms InitECandidate.Solver.Rlp.Validation.loop_body_shape
#print axioms InitECandidate.Solver.Rlp.Validation.original_code

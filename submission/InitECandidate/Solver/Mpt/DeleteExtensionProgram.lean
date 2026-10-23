import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__delete_ext_finish with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one),(ofString "seg",.one),(ofString "sl",.one),(ofString "nc",.one)]
def nullGuard : ProgHOL 64:=match body with | .seq first _=>first | _=>.skip
def tagScope : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip
def afterTag : ProgHOL 64:=match tagScope with | .dec _ _ _ rest=>rest | _=>.skip
def branchGuard : ProgHOL 64:=match afterTag with | .seq first _=>first | _=>.skip
def afterBranch : ProgHOL 64:=match afterTag with | .seq _ rest=>rest | _=>.skip
def hashGuard : ProgHOL 64:=match afterBranch with | .seq first _=>first | _=>.skip
def concatScope : ProgHOL 64:=match afterBranch with | .seq _ rest=>rest | _=>.skip
def lengthScope : ProgHOL 64:=match concatScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match lengthScope with | .dec _ _ _ rest=>rest | _=>.skip
def extensionGuard : ProgHOL 64:=match afterLength with | .seq first _=>first | _=>.skip
def leafTail : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip
def field (name : String) (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar name,.const offset])
def concatArguments : List (ExpHOL 64):=[localVar "seg",localVar "sl",field "nc" 32#64,field "nc" 40#64]
def lengthExpression : ExpHOL 64:=.op .add [localVar "sl",field "nc" 40#64]
def extensionArguments : List (ExpHOL 64):=[localVar "cat",localVar "cl",field "nc" 48#64]
def leafArguments : List (ExpHOL 64):=[localVar "cat",localVar "cl",field "nc" 48#64,field "nc" 56#64]
def branchFinish : ProgHOL 64:=.seq (.store (.op .add [localVar "node",.const 48#64]) (localVar "nc")) (.return (localVar "node"))

theorem entry_shapes : body=.seq nullGuard tagScope ∧
    nullGuard=.ite (.cmp .equal (localVar "nc") (.const 0#64)) (.return (.const 0#64)) .skip ∧
    tagScope=.dec (ofString "ck") .one (field "nc" 0#64) afterTag ∧ afterTag=.seq branchGuard afterBranch ∧
    branchGuard=.ite (.cmp .equal (localVar "ck") (.const 3#64)) branchFinish .skip := by
  simp only [body,nullGuard,tagScope,afterTag,branchGuard,afterBranch,field,branchFinish,Guest.guestFn__delete_ext_finish,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

theorem merge_shapes : afterBranch=.seq hashGuard concatScope ∧
    hashGuard=.ite (.cmp .equal (localVar "ck") (.const 0#64)) (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]) .skip ∧
    concatScope=.decCall (ofString "cat") .one (ofString "nibbles_concat") concatArguments lengthScope ∧
    lengthScope=.dec (ofString "cl") .one lengthExpression afterLength ∧ afterLength=.seq extensionGuard leafTail ∧
    extensionGuard=.ite (.cmp .equal (localVar "ck") (.const 2#64)) (.call none (ofString "node_new_ext") extensionArguments) .skip ∧
    leafTail=.call none (ofString "node_new_leaf") leafArguments := by
  simp only [afterBranch,hashGuard,concatScope,lengthScope,afterLength,extensionGuard,leafTail,concatArguments,lengthExpression,
    extensionArguments,leafArguments,field,afterTag,tagScope,body,Guest.guestFn__delete_ext_finish,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_delete_ext_finish")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 253 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__delete_ext_finish) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__delete_ext_finish,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.entry_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.merge_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.original_code

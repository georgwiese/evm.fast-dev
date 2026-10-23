import InitECandidate.Solver.Mpt.DeleteBodyProgram

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__mpt_delete_node with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=DeleteBody.formals
def afterMark : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterError : ProgHOL 64:=match afterMark with | .dec _ _ _ rest=>rest | _=>.skip
def afterResult : ProgHOL 64:=match afterError with | .dec _ _ _ rest=>rest | _=>.skip
def caughtCall : ProgHOL 64:=match afterResult with | .seq first _=>first | _=>.skip
def afterCall : ProgHOL 64:=match afterResult with | .seq _ rest=>rest | _=>.skip
def arguments : List (ExpHOL 64):=[localVar "node",localVar "key",localVar "klen",localVar "level"]
def releaseArguments : List (ExpHOL 64):=[localVar "mark"]
def release : ProgHOL 64:=.call (some (none,none)) (ofString "scratch_release") releaseArguments
def handler : ProgHOL 64:=.seq release (.raise (ofString "MptErr") (localVar "e"))
def footer : ProgHOL 64:=.return (localVar "res")

theorem shapes : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark ∧
    afterMark=.dec (ofString "e") .one (.const 0#64) afterError ∧
    afterError=.dec (ofString "res") .one (.const 0#64) afterResult ∧
    afterResult=.seq caughtCall afterCall ∧ afterCall=.seq release footer ∧
    caughtCall=.call (some (some (.local,ofString "res"),some (ofString "MptErr",ofString "e",handler))) (ofString "_mpt_delete_node_body") arguments := by
  simp only [body,afterMark,afterError,afterResult,caughtCall,afterCall,arguments,releaseArguments,release,handler,footer,
    Guest.guestFn__mpt_delete_node,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar] <;> simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_mpt_delete_node")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 255 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__mpt_delete_node) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,DeleteBody.formals,body,Guest.guestFn__mpt_delete_node,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.shapes
#print axioms InitECandidate.Solver.Mpt.DeleteNode.original_code

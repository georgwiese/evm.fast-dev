import InitECandidate.Solver.Mpt.NodeRefLenCall
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__node_rlp_finish with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "fr",.one),(ofString "node",.one)]
def afterTag : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterPayload : ProgHOL 64:=match afterTag with | .dec _ _ _ rest=>rest | _=>.skip
def afterBuffer : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match afterBuffer with | .dec _ _ _ rest=>rest | _=>.skip
def afterExtension : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip
def branchChoice : ProgHOL 64:=match afterExtension with | .seq first _=>first | _=>.skip
def branchScope : ProgHOL 64:=match branchChoice with | .ite _ yes _=>yes | _=>.skip
def scanAndAfter : ProgHOL 64:=match branchScope with | .dec _ _ _ rest=>rest | _=>.skip
def scanLoop : ProgHOL 64:=match scanAndAfter with | .seq first _=>first | _=>.skip
def afterScan : ProgHOL 64:=match scanAndAfter with | .seq _ rest=>rest | _=>.skip
def scanBody : ProgHOL 64:=match scanLoop with | .while _ rest=>rest | _=>.skip
def scanTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 16#64)
def childArguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "node",.const 32#64,.panop .mul [localVar "i",.const 8#64]])]
def addLength : ProgHOL 64:=.assign .local (ofString "payload") (.op .add [localVar "payload",localVar "rl2"])
def advance : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def valueArguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "node",.const 160#64]),.load .one (.op .add [localVar "node",.const 168#64])]
def addValue : ProgHOL 64:=.assign .local (ofString "payload") (.op .add [localVar "payload",localVar "vl2"])

set_option maxRecDepth 100000 in
theorem scan_shapes : scanLoop=.while scanTest scanBody ∧
    scanBody=.decCall (ofString "rl2") .one (ofString "node_ref_len") childArguments (.seq addLength advance) ∧
    branchChoice=.ite (.cmp .equal (localVar "k") (.const 3#64)) (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)) .skip := by
  simp only [scanLoop,scanTest,scanBody,scanAndAfter,afterScan,branchScope,branchChoice,afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    childArguments,addLength,advance,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem after_scan_shape : afterScan=.decCall (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments addValue := by
  simp only [afterScan,scanAndAfter,branchScope,branchChoice,afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,valueArguments,addValue,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_finish")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 258 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__node_rlp_finish) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__node_rlp_finish,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.after_scan_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.original_code

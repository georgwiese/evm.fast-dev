import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordEnvironment

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__collapse_branch with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def afterCount : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterIndex : ProgHOL 64:=match afterCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterCounter : ProgHOL 64:=match afterIndex with | .dec _ _ _ rest=>rest | _=>.skip
def scan : ProgHOL 64:=match afterCounter with | .seq first _=>first | _=>.skip
def afterScan : ProgHOL 64:=match afterCounter with | .seq _ rest=>rest | _=>.skip
def scanBody : ProgHOL 64:=match scan with | .while _ inner=>inner | _=>.skip
def scanChoice : ProgHOL 64:=match scanBody with | .seq first _=>first | _=>.skip
def scanAdvance : ProgHOL 64:=match scanBody with | .seq _ rest=>rest | _=>.skip
def childAddress (index : ExpHOL 64) : ExpHOL 64:=.op .add [localVar "node",.const 32#64,.panop .mul [index,.const 8#64]]
def scanTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 16#64)
def selected : ProgHOL 64:=.seq (.assign .local (ofString "count") (.op .add [localVar "count",.const 1#64]))
  (.assign .local (ofString "idx") (localVar "i"))

theorem setup_shapes : body=.dec (ofString "count") .one (.const 0#64) afterCount ∧
    afterCount=.dec (ofString "idx") .one (.const 0#64) afterIndex ∧
    afterIndex=.dec (ofString "i") .one (.const 0#64) afterCounter ∧ afterCounter=.seq scan afterScan := by
  simp only [body,afterCount,afterIndex,afterCounter,scan,afterScan,Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none]
  simp

theorem scan_shapes : scan=.while scanTest scanBody ∧ scanBody=.seq scanChoice scanAdvance ∧
    scanChoice=.ite (.cmp .notEqual (.load .one (childAddress (localVar "i"))) (.const 0#64)) selected .skip ∧
    scanAdvance=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]) := by
  simp only [scan,scanTest,scanBody,scanChoice,scanAdvance,selected,childAddress,afterCounter,afterIndex,afterCount,body,
    Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_collapse_branch")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 252 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__collapse_branch) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__collapse_branch,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (known : source.code.lookup (ofString "_collapse_branch")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite source.code.lookup (ofString "_collapse_branch") [.val (.word node)]=some (body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) :=
  Input.word_environment source.code.lookup (ofString "_collapse_branch") (ofString "node") body .one node known

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.setup_shapes
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_shapes
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.original_code
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.environment

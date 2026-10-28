import InitECandidate.Solver.Input.CurrentHash.FixedRecordProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Kind where | deposit | wdreq | cons | bdep | bexit
  deriving DecidableEq

def Kind.record : Kind→FixedRecord.Kind | .deposit=>.deposit | .wdreq=>.wdreq | .cons=>.cons | .bdep=>.bdep | .bexit=>.bexit
def Kind.tag : Kind→Nat | .deposit=>0 | .wdreq=>1 | .cons=>2 | .bdep=>3 | .bexit=>4
def kinds : List Kind := [.deposit,.wdreq,.cons,.bdep,.bexit]
def body : ProgHOL 64 := Code.body .htr_request_list
def formals : List (MlS×ShapeHOL) := [(ofString "kind",.one),(ofString "p",.one),(ofString "n",.one),(ofString "sz",.one),(ofString "out",.one)]
def arguments : List (ExpHOL 64) := [.op .add [localVar "p",.panop .mul [localVar "i",localVar "sz"]],
  .op .add [localVar "roots",.panop .mul [localVar "i",.const 32#64]]]
def branchTest (kind : Kind) : ExpHOL 64 := .cmp .equal (localVar "kind") (.const (BitVec.ofNat 64 kind.tag))
def branch (kind : Kind) : ProgHOL 64 := .ite (branchTest kind) (.call (some (none,none)) kind.record.name arguments) .skip
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def chain (branches : List Kind) : ProgHOL 64 := branches.foldr (fun kind rest=>.seq (branch kind) rest) increment
def step : ProgHOL 64 := chain kinds
def test : ExpHOL 64 := .cmp .less (localVar "i") (localVar "n")
def loop : ProgHOL 64 := .while test step
def listArguments : List (ExpHOL 64) := [localVar "roots",localVar "n",localVar "n",localVar "out"]
def afterLoop : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) FixedRecord.releaseSuffix
def loopAndSuffix : ProgHOL 64 := .seq loop afterLoop
def afterRoots : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) loopAndSuffix
def allocationArguments : List (ExpHOL 64) := [.op .add [.panop .mul [localVar "n",.const 32#64],.const 32#64]]
def afterMark : ProgHOL 64 := .decCall (ofString "roots") .one (ofString "alloc") allocationArguments afterRoots

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,afterMark,afterRoots,loopAndSuffix,loop,step,kinds,chain,List.foldr_cons,List.foldr_nil,branch,branchTest,increment,test,
    afterLoop,FixedRecord.releaseSuffix,listArguments,arguments,allocationArguments,Kind.record,Kind.tag,FixedRecord.Kind.name,FixedRecord.Kind.routine,Code.name,
    Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_request_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_request_list")=some (formals,body,.one) := by
  simpa only [Code.name,Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,body,formals,
    GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_request_list,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using Code.installed code installed .htr_request_list

theorem tag_injective (a b : Kind) : BitVec.ofNat 64 a.tag=BitVec.ofNat 64 b.tag ↔ a=b := by cases a <;> cases b <;> decide

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.body_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.original_code
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.tag_injective

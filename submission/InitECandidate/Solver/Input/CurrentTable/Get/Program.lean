import InitECandidate.Solver.Input.CurrentTable.Image
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Call
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_get with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "t",.one),(ofString "key",.one)]
def resultShape : ShapeHOL := .comb [.one,.one]
def lookupArguments : List (ExpHOL 64) := [localVar "t",localVar "key"]
def header (offset : Nat) : ExpHOL 64 := .op .add [localVar "t",.const (BitVec.ofNat 64 offset)]
def absent : ProgHOL 64 := .return (.rstruct [.const 0#64,.const 0#64])
def emptyGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "leaf") (.const 0#64)) absent .skip
def compareArguments : List (ExpHOL 64) :=
  [.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "key",localVar "klen"]
def valueRead : ExpHOL 64 := .load .one (.op .add [.load .one (header 40),.panop .mul [localVar "leaf",.const 32#64],.const 8#64])
def compareGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "eq") (.const 0#64)) absent .skip
def afterCompare : ProgHOL 64 := .seq compareGuard (.return (.rstruct [.const 1#64,valueRead]))
def compareCall : ProgHOL 64 := .decCall (ofString "eq") .one (ofString "memeq") compareArguments afterCompare
def afterStride : ProgHOL 64 := .dec (ofString "keys") .one (.load .one (header 32)) compareCall
def afterLength : ProgHOL 64 := .dec (ofString "stride") .one (.load .one (header 8)) afterStride
def afterEmpty : ProgHOL 64 := .dec (ofString "klen") .one (.load .one (header 0)) afterLength
def afterLeaf : ProgHOL 64 := .seq emptyGuard afterEmpty

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "leaf") .one (ofString "htab_find_leaf") lookupArguments afterLeaf := by
  simp only [body,Guest.Software.guestFn_htab_get,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    lookupArguments,afterLeaf,emptyGuard,absent,afterEmpty,afterLength,afterStride,compareCall,compareArguments,afterCompare,compareGuard,valueRead,header,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_get")=some (formals,body,resultShape) := by
  have checked := OriginalCode.indexed code installed 120 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_get) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_htab_get,
    body,formals,resultShape,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.body_shape
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.original_code

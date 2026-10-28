import InitECandidate.Solver.Input.CurrentTable.Get.Call

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_nodedb_lookup with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "db",.one),(ofString "hash",.one)]
def resultShape : ShapeHOL := .comb [.one,.one,.one]
def arguments : List (ExpHOL 64) := [localVar "db",localVar "hash"]
def recordPointer : ExpHOL 64 := .rfield 1 (localVar "r")
def absentValue : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
def presentValue (pointer length : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word 1#64),.val (.word pointer),.val (.word length)]
def absent : ProgHOL 64 := .return (.rstruct [.const 0#64,.const 0#64,.const 0#64])
def guard : ProgHOL 64 := .ite (.cmp .equal (.rfield 0 (localVar "r")) (.const 0#64)) absent .skip
def present : ProgHOL 64 := .return (.rstruct [.const 1#64,.load .one recordPointer,.load .one (.op .add [recordPointer,.const 8#64])])
def afterGet : ProgHOL 64 := .seq guard present

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "r") Get.resultShape (ofString "htab_get") arguments afterGet := by
  simp only [body,Guest.Software.guestFn_nodedb_lookup,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Get.resultShape,arguments,afterGet,guard,absent,present,recordPointer,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "nodedb_lookup")=some (formals,body,resultShape) := by
  have checked := OriginalCode.indexed code installed 228 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_nodedb_lookup) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_nodedb_lookup,
    body,formals,resultShape,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.body_shape
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.original_code

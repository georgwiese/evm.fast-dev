import InitECandidate.Solver.Rlp.HeaderProgram

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_list_to_slices with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def afterCount : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterAlloc : ProgHOL 64 := match afterCount with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64 := match afterAlloc with | .dec _ _ _ (.dec _ _ _ (.seq first _))=>first | _=>.skip
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "count")
def cell : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]
def advances : ProgHOL 64 := .seq (.assign .local (ofString "off") (.op .add [localVar "off",localVar "total"]))
  (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))
def stores : ProgHOL 64 := .seq (.store cell (.op .add [localVar "p",localVar "off"]))
  (.seq (.store (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]) (localVar "total")) advances)
def loopBody : ProgHOL 64 := .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked") [.op .add [localVar "p",localVar "off"]] stores
def resultShape : ShapeHOL := .comb [.one,.one]
def returnArray : ProgHOL 64 := .return (.rstruct [localVar "arr",localVar "count"])
def allocationArguments : List (ExpHOL 64) := [.panop .mul [localVar "count",.const 16#64]]

set_option maxRecDepth 10000
theorem body_shape : body=.decCall (ofString "count") .one (ofString "rlp_list_count") arguments afterCount := by
  simp only [body,arguments,afterCount,localVar,Guest.Software.guestFn_rlp_list_to_slices,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem after_count_shape : afterCount=.decCall (ofString "arr") .one (ofString "alloc") allocationArguments afterAlloc := by
  simp only [afterCount,body,afterAlloc,allocationArguments,localVar,Guest.Software.guestFn_rlp_list_to_slices,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem after_alloc_shape : afterAlloc=.dec (ofString "i") .one (.const 0#64)
    (.dec (ofString "off") .one (.const 0#64) (.seq loop returnArray)) := by
  simp only [afterAlloc,afterCount,body,loop,returnArray,localVar,Guest.Software.guestFn_rlp_list_to_slices,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,afterAlloc,afterCount,body,condition,loopBody,stores,cell,advances,localVar,
    Guest.Software.guestFn_rlp_list_to_slices,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_list_to_slices")=some (Header.formals,body,resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 103 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_list_to_slices) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,resultShape,
    Guest.Software.guestFn_rlp_list_to_slices,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.body_shape
#print axioms InitECandidate.Solver.Rlp.Slices.after_count_shape
#print axioms InitECandidate.Solver.Rlp.Slices.after_alloc_shape
#print axioms InitECandidate.Solver.Rlp.Slices.loop_shape
#print axioms InitECandidate.Solver.Rlp.Slices.original_code

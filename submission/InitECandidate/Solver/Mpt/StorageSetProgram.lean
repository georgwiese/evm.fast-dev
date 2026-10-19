import InitECandidate.Solver.Mpt.TransientSetProgram
import InitECandidate.Solver.MutableTable.GetCall32

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_set_storage with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := TransientSet.formals
def table : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ts"),.const 32#64])
def setCall : ProgHOL 64 := .call (some (none,none)) (ofString "jset") [localVar "inner",localVar "key",localVar "v"]
def afterAlloc : ProgHOL 64 := .seq (.store (localVar "v") (localVar "value")) (.seq setCall (.return (.const 0#64)))
def allocate : ProgHOL 64 := .decCall (ofString "v") .one (ofString "alloc") [.const 32#64] afterAlloc
def publishCall : ProgHOL 64 := .call (some (none,none)) (ofString "jset") [localVar "outer",localVar "addr",localVar "inner"]
def newCall : ProgHOL 64 := .call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32#64,.const 8#64]
def choose : ProgHOL 64 := .ite (.cmp .equal (.rfield 0 (localVar "m")) (.const 0#64))
  (.seq newCall publishCall) (.assign .local (ofString "inner") (.rfield 1 (localVar "m")))
def afterGet : ProgHOL 64 := .dec (ofString "inner") .one (.const 0#64) (.seq choose allocate)
def getter : ProgHOL 64 := .decCall (ofString "m") Get.pairShape (ofString "htab_get") [localVar "outer",localVar "addr"] afterGet
def afterAccount : ProgHOL 64 := .seq (.ite (.cmp .equal (localVar "a") (.const 1#64)) (.raise (ofString "StateErr") (.const 3#64)) .skip)
  (.dec (ofString "outer") .one table getter)

theorem body_shape : body = .decCall (ofString "a") .one (ofString "get_account_optional") [localVar "addr"] afterAccount := by
  simp only [body,afterAccount,getter,afterGet,choose,newCall,publishCall,allocate,afterAlloc,setCall,table,localVar,Get.pairShape,Guest.guestFn_set_storage,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "set_storage") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 356 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_set_storage) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,TransientSet.formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_set_storage,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.body_shape
#print axioms InitECandidate.Solver.Mpt.StorageSet.original_code

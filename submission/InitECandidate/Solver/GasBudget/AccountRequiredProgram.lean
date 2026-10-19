import InitECandidate.Solver.GasBudget.AccountCacheProgram

namespace InitECandidate.Solver.GasBudget.AccountRequired
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : AccountCache.Kind → ProgHOL 64
  | .transaction => match Guest.guestFn_get_account with | .function fn=>progToHOL fn.body | _=>.skip
  | .preState => match Guest.guestFn_get_pre_state_account with | .function fn=>progToHOL fn.body | _=>.skip
def name : AccountCache.Kind → String | .transaction=>"get_account" | .preState=>"get_pre_state_account"
def optionalName : AccountCache.Kind → String | .transaction=>"get_account_optional" | .preState=>"get_pre_state_account_optional"
def formals : List (MlS×ShapeHOL) := [(ofString "addr",.one)]
def emptyCall : ProgHOL 64 := .call (some (some (.local,ofString "a"),none)) (ofString "acct_empty") []
def afterGet : ProgHOL 64 := .seq (.ite (.cmp .equal (localVar "a") (.const 1#64)) emptyCall .skip) (.return (localVar "a"))

theorem body_shape (kind : AccountCache.Kind) : body kind=.decCall (ofString "a") .one (ofString (optionalName kind)) [localVar "addr"] afterGet := by
  cases kind <;> simp only [body,optionalName,Guest.guestFn_get_account,Guest.guestFn_get_pre_state_account,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,afterGet,emptyCall,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) (kind : AccountCache.Kind) :
    code.lookup (ofString (name kind))=some (formals,body kind,.one) := by
  cases kind with
  | transaction =>
    have checked := Input.OriginalCode.indexed code installed 343 (OriginalCodeEnvironment.originalEntry Guest.guestFn_get_account) (by rfl)
    simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,name,formals,Guest.guestFn_get_account,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | preState =>
    have checked := Input.OriginalCode.indexed code installed 341 (OriginalCodeEnvironment.originalEntry Guest.guestFn_get_pre_state_account) (by rfl)
    simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,name,formals,Guest.guestFn_get_pre_state_account,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem fallback_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (cell : source.locals.lookup (ofString "a")=some (.val (.word value))) :
    evaluateHOLFiniteState source afterGet=if value=1#64 then evaluateHOLFiniteState source (.seq emptyCall (.return (localVar "a")))
      else (some (.returned (.val (.word value))),emptyLocalsHOLFinite source) := by
  rw [afterGet,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  by_cases absent : value=1#64
  all_goals simp [evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,
    evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.GasBudget.AccountRequired

#print axioms InitECandidate.Solver.GasBudget.AccountRequired.body_shape
#print axioms InitECandidate.Solver.GasBudget.AccountRequired.original_code
#print axioms InitECandidate.Solver.GasBudget.AccountRequired.fallback_dispatch

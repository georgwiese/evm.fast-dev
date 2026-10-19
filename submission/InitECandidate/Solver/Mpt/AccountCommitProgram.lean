import InitECandidate.Solver.Mpt.AccountSetCallRegistered
import InitECandidate.Solver.Mpt.AccountIsEmptyCall

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def destroyBody : ProgHOL 64 := match Guest.guestFn_destroy_account with | .function fn => progToHOL fn.body | _ => .skip
def destroyFormals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def destroyStorageCall : ProgHOL 64 := .call (some (none,none)) (ofString "destroy_storage") [localVar "addr"]
def eraseAccountCall : ProgHOL 64 := .call (some (none,none)) (ofString "set_account") [localVar "addr",.const 1#64]
def body : ProgHOL 64 := match Guest.guestFn_modify_state_commit with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one),(ofString "a",.one)]
def publishCall : ProgHOL 64 := .call (some (none,none)) (ofString "set_account") [localVar "addr",localVar "a"]
def destroyCall : ProgHOL 64 := .call (some (none,none)) (ofString "destroy_account") [localVar "addr"]
def afterEmpty : ProgHOL 64 := .seq (.ite (.cmp .notEqual (localVar "e") (.const 0#64)) destroyCall .skip) (.return (.const 0#64))

theorem destroy_shape : destroyBody = .seq destroyStorageCall (.seq eraseAccountCall (.return (.const 0#64))) := by
  simp only [destroyBody,destroyStorageCall,eraseAccountCall,localVar,Guest.guestFn_destroy_account,progToHOL,expToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]

theorem body_shape : body = .seq publishCall (.decCall (ofString "e") .one (ofString "acct_is_empty") [localVar "a"] afterEmpty) := by
  simp only [body,publishCall,afterEmpty,destroyCall,localVar,Guest.guestFn_modify_state_commit,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem destroy_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "destroy_account") = some (destroyFormals,destroyBody,.one) := by
  have checked := Input.OriginalCode.indexed code installed 358 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_destroy_account) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,destroyBody,destroyFormals,Guest.guestFn_destroy_account,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "modify_state_commit") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 359 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_modify_state_commit) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_modify_state_commit,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem empty_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (empty : BitVec 64)
    (cell : source.locals.lookup (ofString "e") = some (.val (.word empty))) :
    evaluateHOLFiniteState source afterEmpty = if empty = 0#64 then
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source)
      else evaluateHOLFiniteState source (.seq destroyCall (.return (.const 0#64))) := by
  classical
  by_cases zero : empty = 0#64
  all_goals simp [afterEmpty,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,
    evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,shapeOfHOLExact]

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.destroy_shape
#print axioms InitECandidate.Solver.Mpt.AccountCommit.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountCommit.destroy_code
#print axioms InitECandidate.Solver.Mpt.AccountCommit.original_code
#print axioms InitECandidate.Solver.Mpt.AccountCommit.empty_dispatch

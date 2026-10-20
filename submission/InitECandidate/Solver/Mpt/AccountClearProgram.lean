import InitECandidate.Solver.Mpt.AccountResetFields
import InitECandidate.Solver.Mpt.AccountCommitProgram

namespace InitECandidate.Solver.Mpt.AccountClear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

def body : ProgHOL 64 := match Guest.guestFn_clear_account_preserving_balance with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def destroyCall : ProgHOL 64 := .call (some (none,none)) (ofString "destroy_storage") [localVar "addr"]
def copyCall : ProgHOL 64 := .call (some (some (.local,ofString "a"),none)) (ofString "acct_copy") [localVar "a"]
def commitCall : ProgHOL 64 := .call (some (none,none)) (ofString "modify_state_commit") [localVar "addr",localVar "a"]
def afterCopy : ProgHOL 64 := .seq (.store (.op .add [localVar "a",.const 0#64]) (.const 0#64))
  (.seq (.store (.op .add [localVar "a",.const 48#64]) (.var .global (ofString "empty_code_hash")))
    (.seq commitCall (.return (.const 0#64))))
def afterGet : ProgHOL 64 := .seq copyCall afterCopy
def afterDestroy : ProgHOL 64 := .decCall (ofString "a") .one (ofString "get_account") [localVar "addr"] afterGet

theorem body_shape : body = .seq destroyCall afterDestroy := by
  simp only [body,destroyCall,afterDestroy,afterGet,copyCall,afterCopy,commitCall,localVar,Guest.guestFn_clear_account_preserving_balance,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem after_copy_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evaluateHOLFiniteState source afterCopy = evaluateHOLFiniteState source (.seq (AccountMutation.resetFields "a") (.seq commitCall (.return (.const 0#64)))) :=
  (MemeqByteRuntime.sequence_assoc source (.store (.op .add [localVar "a",.const 0#64]) (.const 0#64))
    (.store (.op .add [localVar "a",.const 48#64]) (.var .global (ofString "empty_code_hash"))) (.seq commitCall (.return (.const 0#64)))).symm

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "clear_account_preserving_balance") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 360 (OriginalCodeEnvironment.originalEntry Guest.guestFn_clear_account_preserving_balance) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_clear_account_preserving_balance,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountClear

#print axioms InitECandidate.Solver.Mpt.AccountClear.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountClear.after_copy_execute
#print axioms InitECandidate.Solver.Mpt.AccountClear.original_code

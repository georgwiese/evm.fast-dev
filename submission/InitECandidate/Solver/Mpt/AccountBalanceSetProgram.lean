import InitECandidate.Solver.Mpt.AccountCommitProgram
import InitECandidate.Solver.GasBudget.AccountRequiredProgram

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_set_account_balance with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one),(ofString "amount",Input.RlpWrite.U256Value.tupleShape)]
def copyCall : ProgHOL 64 := .call (some (some (.local,ofString "a"),none)) (ofString "acct_copy") [localVar "a"]
def balanceStore : ProgHOL 64 := .store (.op .add [localVar "a",.const 8#64]) (localVar "amount")
def commitCall : ProgHOL 64 := .call (some (none,none)) (ofString "modify_state_commit") [localVar "addr",localVar "a"]
def afterCopy : ProgHOL 64 := .seq balanceStore (.seq commitCall (.return (.const 0#64)))
def afterGet : ProgHOL 64 := .seq copyCall afterCopy

theorem body_shape : body = .decCall (ofString "a") .one (ofString "get_account") [localVar "addr"] afterGet := by
  simp only [body,afterGet,afterCopy,copyCall,balanceStore,commitCall,localVar,Guest.guestFn_set_account_balance,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "set_account_balance") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 365 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_set_account_balance) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_set_account_balance,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.original_code

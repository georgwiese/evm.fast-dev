import InitECandidate.Solver.Mpt.AccountBalanceMutation
import InitECandidate.Solver.GasBudget.U256ArithmeticCall
import InitECandidate.Solver.GasBudget.U256ArithmeticAssigned
import InitECandidate.Solver.GasBudget.U256LessThanCall

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

def body : ProgHOL 64 := match Guest.guestFn_move_ether with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "sender",.one),(ofString "recipient",.one),(ofString "amount",Input.RlpWrite.U256Value.tupleShape)]
def balanceArguments (name : String) : List (ExpHOL 64) := [.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar name,.const 8#64]),localVar "amount"]
def copyAccount (name : String) : ProgHOL 64 := .call (some (some (.local,ofString name),none)) (ofString "acct_copy") [localVar name]
def recipientCommit : ProgHOL 64 := .seq (AccountBalanceSet.storeBalanceAt "r" (localVar "nb"))
  (.seq (AccountBalanceSet.commitAccounts "recipient" "r") (.return (.const 0#64)))
def afterRecipient : ProgHOL 64 := .seq (copyAccount "r")
  (.seq (.call (some (some (.local,ofString "nb"),none)) (ofString "u256_add") (balanceArguments "r")) recipientCommit)
def recipient : ProgHOL 64 := .decCall (ofString "r") .one (ofString "get_account") [localVar "recipient"] afterRecipient
def senderCommit : ProgHOL 64 := .seq (AccountBalanceSet.storeBalanceAt "s" (localVar "nb"))
  (.seq (AccountBalanceSet.commitAccounts "sender" "s") recipient)
def afterCopy : ProgHOL 64 := .decCall (ofString "nb") Input.RlpWrite.U256Value.tupleShape (ofString "u256_sub") (balanceArguments "s") senderCommit
def guard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "lt") (.const 0#64)) (.raise (ofString "StateErr") (.const 4#64)) .skip
def afterCompare : ProgHOL 64 := .seq guard (.seq (copyAccount "s") afterCopy)
def afterSender : ProgHOL 64 := .decCall (ofString "lt") .one (ofString "u256_lt") (balanceArguments "s") afterCompare

theorem body_shape : body = .decCall (ofString "s") .one (ofString "get_account") [localVar "sender"] afterSender := by
  simp only [body,afterSender,afterCompare,guard,copyAccount,afterCopy,senderCommit,recipient,afterRecipient,recipientCommit,balanceArguments,
    AccountBalanceSet.storeBalanceAt,AccountBalanceSet.commitAccounts,Input.RlpWrite.U256Value.tupleShape,localVar,Guest.guestFn_move_ether,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "move_ether") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 363 (OriginalCodeEnvironment.originalEntry Guest.guestFn_move_ether) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_move_ether,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem guard_safe : Input.PureGuard guard := .ite _ (.raise _ _) .skip

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.original_code
#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.guard_safe

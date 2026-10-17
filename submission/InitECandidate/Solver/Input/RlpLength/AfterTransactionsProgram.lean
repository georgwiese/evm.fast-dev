import InitECandidate.Solver.Input.RlpLength.TransactionDecoded
import InitECandidate.Solver.Input.RlpLength.BlockWithdrawalPhase

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionSuffix : ProgHOL 64 := ((loopTails body)[0]?).getD .skip
def addTransactionsExpression : ExpHOL 64 := .op .add [localVar "total",localVar "hl",localVar "tl"]
def addOmmersExpression : ExpHOL 64 := .op .add [localVar "total",.const 1#64]
def withdrawalCountExpression : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const 56#64])
def enterWithdrawals : ProgHOL 64 := .dec (ofString "nwd") .one withdrawalCountExpression
  (.dec (ofString "wl") .one (.const 0#64) (.seq (.assign .local (ofString "i") (.const 0#64)) withdrawalPhase))
def afterTransactionHeader : ProgHOL 64 := .seq (.assign .local (ofString "total") addTransactionsExpression)
  (.seq (.assign .local (ofString "total") addOmmersExpression) enterWithdrawals)

theorem transaction_suffix_shape : transactionSuffix=.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "tl"] afterTransactionHeader := by
  simp only [transactionSuffix,loopTails,body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,
    afterTransactionHeader,addTransactionsExpression,addOmmersExpression,enterWithdrawals,withdrawalCountExpression,withdrawalPhase]
  rw [loop_shape,suffix_shape]
  rfl

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.transaction_suffix_shape

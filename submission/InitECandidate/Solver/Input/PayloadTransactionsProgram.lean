import InitECandidate.Solver.Input.PayloadExtraGuard
import InitECandidate.Solver.Input.VarList.CallerNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extraPointerValue : ExpHOL 64 := .op .add [localVar "p",localVar "o_extra"]
def extraPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 16) extraPointerValue
def extraLengthStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 24) extraLength
def transactionArguments : List (ExpHOL 64) := [
  .op .add [localVar "p",localVar "o_txs"],
  .op .sub [localVar "o_wd",localVar "o_txs"],.const 9223372036854775807#64]
def transactionCall : ProgHOL 64 := dropLeading 2 afterExtra
def afterTransactions : ProgHOL 64 := match transactionCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def transactionPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 32) (.rfield 0 (localVar "txs"))
def transactionCountStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 40) (.rfield 1 (localVar "txs"))
def withdrawalArguments : List (ExpHOL 64) := [
  .op .sub [localVar "o_bal",localVar "o_wd"],.const 44#64,.const 9223372036854775807#64]
def withdrawalCall : ProgHOL 64 := dropLeading 2 afterTransactions
def afterWithdrawals : ProgHOL 64 := match withdrawalCall with | .decCall _ _ _ _ rest=>rest | _=>.skip

theorem transactions_shape : afterExtra=.seq extraPointerStore (.seq extraLengthStore transactionCall) ∧
    transactionCall=.decCall (ofString "txs") VarList.returnShape (ofString "ssz_split_var_list") transactionArguments afterTransactions ∧
    afterTransactions=.seq transactionPointerStore (.seq transactionCountStore withdrawalCall) ∧
    withdrawalCall=.decCall (ofString "nwd") .one (ofString "ssz_fixed_list_count") withdrawalArguments afterWithdrawals := by
  simp only [afterExtra,offsetContinuation,offsetBody,dropLeading,afterGuard,body,Scalar.payloadBody,Guest.guestFn_decode_payload,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    extraPointerStore,extraPointerValue,extraLengthStore,extraLength,transactionCall,afterTransactions,
    transactionPointerStore,transactionCountStore,withdrawalCall,afterWithdrawals,transactionArguments,withdrawalArguments,
    Scalar.plus,localVar,VarList.returnShape]
  simp

theorem transaction_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (ordered : Guest.GasLimit.le32 input 566≤Guest.GasLimit.le32 input 570)
    (contained : 62+Guest.GasLimit.le32 input 570≤input.length%2^64) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionArguments=
      some (VarList.values (pointer+BitVec.ofNat 64 (62+Guest.GasLimit.le32 input 566))
        (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)) 9223372036854775807#64) ∧
      (62+Guest.GasLimit.le32 input 566)+(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)≤input.length%2^64 := by
  classical
  have subtraction:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (Guest.GasLimit.le32 input 570) (Guest.GasLimit.le32 input 566)
    (by have bound:=RawScalar.le32_lt input 566; omega) ordered
  refine ⟨?_,by omega⟩
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,transactionArguments,localVar,p,t,w,offsetWords,
    VarList.values,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc,←BitVec.ofNat_add,subtraction]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.transactions_shape
#print axioms InitECandidate.Solver.Input.Payload.transaction_arguments

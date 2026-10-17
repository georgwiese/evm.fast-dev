import InitECandidate.Solver.Input.PayloadFields
import InitECandidate.Solver.Input.PayloadTransactionsProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def remainingFields (input : Guest.InputBlob) (pointer length withdrawals balances count : BitVec 64) : List Field := [
  (48,.op .add [localVar "p",localVar "o_wd"],pointer+62#64+withdrawals),
  (56,localVar "nwd",count),
  (64,.op .add [localVar "p",localVar "o_bal"],pointer+62#64+balances),
  (72,.op .sub [localVar "len",localVar "o_bal"],length-balances),
  (80,Scalar.flat64 (localVar "p") [404],BitVec.ofNat 64 (Guest.GasLimit.le64 input 466)),
  (88,Scalar.flat64 (localVar "p") [412],BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)),
  (96,Scalar.flat64 (localVar "p") [420],BitVec.ofNat 64 (Guest.GasLimit.le64 input 482)),
  (104,Scalar.flat64 (localVar "p") [428],BitVec.ofNat 64 (Guest.GasLimit.le64 input 490)),
  (112,Scalar.flat64 (localVar "p") [512],BitVec.ofNat 64 (Guest.GasLimit.le64 input 574)),
  (120,Scalar.flat64 (localVar "p") [520],BitVec.ofNat 64 (Guest.GasLimit.le64 input 582)),
  (128,Scalar.flat64 (localVar "p") [532],BitVec.ofNat 64 (Guest.GasLimit.le64 input 594))]

theorem remaining_shape (input : Guest.InputBlob) (pointer length withdrawals balances count : BitVec 64) :
    afterWithdrawals=fieldProgram (remainingFields input pointer length withdrawals balances count) := by
  simp only [afterWithdrawals,withdrawalCall,afterTransactions,transactionCall,afterExtra,offsetContinuation,offsetBody,dropLeading,
    afterGuard,body,Scalar.payloadBody,Guest.guestFn_decode_payload,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    fieldProgram,remainingFields,Scalar.flat64,Scalar.flat32,Scalar.flatAddress,Scalar.shift,Scalar.plus,localVar,List.nil_append,List.cons_append,List.append_nil]

theorem remaining_valid (input : Guest.InputBlob) (pointer length withdrawals balances count : BitVec 64) :
    ∀ field∈remainingFields input pointer length withdrawals balances count,field.1≤128 ∧ field.1%8=0 := by
  intro field mem
  simp only [remainingFields,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Prod.fst] <;> decide

theorem remaining_gas_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length withdrawals balances count : BitVec 64) (room : cursor.toNat+136≤33806089496) :
    (applyFields source cursor (remainingFields input pointer length withdrawals balances count)).memory (cursor+88#64)=
      .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) := by
  have actual:=applyFields_cell source cursor room (remainingFields input pointer length withdrawals balances count)
    (fun field mem=>(remaining_valid input pointer length withdrawals balances count field mem).1) 88 (by decide)
  simpa [cellValue,remainingFields] using actual

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.remaining_shape
#print axioms InitECandidate.Solver.Input.Payload.remaining_valid
#print axioms InitECandidate.Solver.Input.Payload.remaining_gas_cell

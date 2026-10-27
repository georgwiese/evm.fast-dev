import InitECandidate.Solver.Input.PayloadWordStore
import InitECandidate.Solver.Input.FixedList.Environment

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionFieldsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor pointer count : BitVec 64) :=
  fieldStored (fieldStored source cursor 32 pointer) cursor 40 count

theorem transaction_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor records count : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (txs : source.locals.lookup (ofString "txs")=some (UDivMod.pairValue records count))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496) :
    evaluateHOLFiniteState source afterTransactions=evaluateHOLFiniteState (transactionFieldsStored source cursor records count) withdrawalCall ∧
    Blob.HeapInput (transactionFieldsStored source cursor records count) input pointer := by
  classical
  have firstRead : eval source (.rfield 0 (localVar "txs"))=some (.val (.word records)) := by
    simp [eval,localVar,UDivMod.pairValue,evalHOLExact,toExact,txs]
  obtain ⟨firstRun,firstHeap,firstCell,firstFrame⟩:=field_store source input pointer cursor heap pl domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom 32 (by decide) (by decide) (.rfield 0 (localVar "txs")) records firstRead
  let first:=fieldStored source cursor 32 records
  change evaluateHOLFiniteState source transactionPointerStore=(none,first) at firstRun
  have secondRead : eval first (.rfield 1 (localVar "txs"))=some (.val (.word count)) := by
    have saved : first.locals.lookup (ofString "txs")=some (UDivMod.pairValue records count):=txs
    simp [eval,localVar,UDivMod.pairValue,evalHOLExact,toExact,saved]
  obtain ⟨secondRun,secondHeap,secondCell,secondFrame⟩:=field_store first input pointer cursor firstHeap pl domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom 40 (by decide) (by decide) (.rfield 1 (localVar "txs")) count secondRead
  change evaluateHOLFiniteState first transactionCountStore=(none,transactionFieldsStored source cursor records count) at secondRun
  refine ⟨?_,secondHeap⟩
  rw [transactions_shape.2.2.1,WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first (transactionFieldsStored source cursor records count) _ _ secondRun (Nat.le_refl _)]

theorem withdrawal_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (withdrawals balances : BitVec 64)
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word withdrawals)))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word balances))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalArguments=
      some (FixedList.values (balances-withdrawals) 44#64 9223372036854775807#64) := by
  classical
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,withdrawalArguments,FixedList.values,localVar,w,b,valueIsWord,valueWord,wordOpHOL,wordOp]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.transaction_stores
#print axioms InitECandidate.Solver.Input.Payload.withdrawal_arguments

import InitECandidate.Solver.Input.PayloadWordStore

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extraPointerStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor : BitVec 64) :=
  fieldStored source cursor 16 (pointer+602#64)
def extraStoredPayload (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64) :=
  fieldStored (extraPointerStored source pointer cursor) cursor 24 (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566-540))

/-- The two real extra-data stores introduce no clocks and preserve copied
input. The next program is the actual transaction-list call. -/
theorem extra_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (ordered : 540≤Guest.GasLimit.le32 input 566)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496) :
    evaluateHOLFiniteState source afterExtra=evaluateHOLFiniteState (extraStoredPayload source input pointer cursor) transactionCall ∧
    Blob.HeapInput (extraStoredPayload source input pointer cursor) input pointer := by
  classical
  have firstRead : eval source extraPointerValue=some (.val (.word (pointer+602#64))) := by
    simp [eval,extraPointerValue,localVar,evalHOLExact,evalListHOLExact,toExact,p,e,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  obtain ⟨firstRun,firstHeap,firstCell,firstFrame⟩:=field_store source input pointer cursor heap pl domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom 16 (by decide) (by decide) extraPointerValue (pointer+602#64) firstRead
  let first:=extraPointerStored source pointer cursor
  change evaluateHOLFiniteState source extraPointerStore=(none,first) at firstRun
  have subtraction:=BitVec.ofNat_sub_ofNat_of_le (w:=64) (Guest.GasLimit.le32 input 566) 540 (by decide) ordered
  have secondRead : eval first extraLength=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566-540)))) := by
    have e' : first.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)):=e
    have t' : first.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))):=t
    simp [eval,extraLength,localVar,evalHOLExact,evalListHOLExact,toExact,e',t',offsetWords,valueIsWord,valueWord,wordOpHOL,wordOp,subtraction]
  obtain ⟨secondRun,secondHeap,secondCell,secondFrame⟩:=field_store first input pointer cursor firstHeap pl domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom 24 (by decide) (by decide) extraLength _ secondRead
  change evaluateHOLFiniteState first extraLengthStore=(none,extraStoredPayload source input pointer cursor) at secondRun
  refine ⟨?_,secondHeap⟩
  rw [transactions_shape.1,WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first (extraStoredPayload source input pointer cursor) _ _ secondRun (Nat.le_refl _)]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.extra_stores

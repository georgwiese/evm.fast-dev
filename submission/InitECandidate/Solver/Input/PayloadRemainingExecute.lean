import InitECandidate.Solver.Input.PayloadRemainingReads
import InitECandidate.Solver.Input.RawScalar

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

attribute [local irreducible] applyFields remainingFields afterWithdrawals

/-- Complete literal payload suffix after withdrawal counting: all eleven
stores, seven copied uint64 reads and actual return. No further calls or
source clocks occur. In particular later stores preserve the actual gas cell. -/
theorem remaining_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length withdrawals balances count : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word withdrawals)))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word balances)))
    (c : source.locals.lookup (ofString "nwd")=some (.val (.word count)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496) :
    let target:=emptyLocalsHOLFinite (applyFields source cursor (remainingFields input pointer length withdrawals balances count))
    evaluateHOLFiniteState source afterWithdrawals=(some (.returned (.val (.word cursor))),target) ∧
      Blob.HeapInput target input pointer ∧ target.clock=source.clock ∧
      target.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧ target.memory (cursor+56#64)=.word count := by
  have valid:=remaining_valid input pointer length withdrawals balances count
  have reads : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.locals=source.locals→Blob.HeapInput current input pointer→
      ∀ field∈remainingFields input pointer length withdrawals balances count,eval current field.2.1=some (.val (.word field.2.2)) := by
    intro current localsEq currentHeap
    apply remaining_reads current input pointer length withdrawals balances count currentHeap inside
    · rw [localsEq]; exact p
    · rw [localsEq]; exact n
    · rw [localsEq]; exact w
    · rw [localsEq]; exact b
    · rw [localsEq]; exact c
  obtain ⟨run,finalHeap⟩:=fields_execute source input pointer cursor heap pl domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
    (remainingFields input pointer length withdrawals balances count) valid reads
  refine ⟨?_,?_,applyFields_clock source cursor (remainingFields input pointer length withdrawals balances count),remaining_gas_cell source input pointer cursor length withdrawals balances count cursorRoom,remaining_count_cell source input pointer cursor length withdrawals balances count cursorRoom⟩
  · rw [remaining_shape input pointer length withdrawals balances count]
    exact run
  · exact Blob.HeapInput.of_fields (applyFields source cursor (remainingFields input pointer length withdrawals balances count))
      (emptyLocalsHOLFinite (applyFields source cursor (remainingFields input pointer length withdrawals balances count))) input pointer rfl rfl rfl finalHeap

theorem stored_gas_bound (input : Guest.InputBlob)
    (request : Guest.GasLimit.le32 input 2=16) (payload : Guest.GasLimit.le32 input 18=44)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000) :
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)).toNat≤200000000 := by
  rw [RawScalar.le64_number,←Framing.declared_gas_at_474 input request payload]
  exact gas

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.remaining_execute
#print axioms InitECandidate.Solver.Input.Payload.stored_gas_bound

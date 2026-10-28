import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionAllocationCost

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.transaction_after_ntx_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterNtx=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+3 := by
  rw [transaction_shapes.2.2.1] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "m2" afterSecondMark data.context.heap
    (HeapScope.mark_original_code source.code data.context.installed) result actual notTimeout
  let entry := bind {source with clock:=source.clock-1} "m2" cursor
  have next : State input entry blob record array ch cursor chunk out zeros length start size := (data.at_clock (source.clock-1)).bound "m2" cursor (by decide)
  have saved := next.saved_cursor "m2" (bind_lookup_same {source with clock:=source.clock-1} "m2" cursor)
  have kept (name : String) (different : ofString "m2"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "m2" name cursor different
  have paid := next.transaction_after_second_mark_cost (post:=inner) saved ((kept "txs" (by decide)).trans pointer) ((kept "ntx" (by decide)).trans count) result remaining notTimeout
  change source.clock-1-inner.clock≤transactionTailPrice input length start size+2 at paid
  rw [endpoint]
  change source.clock-inner.clock≤transactionTailPrice input length start size+3
  omega

/-- Complete actual transaction phase, with both original lexical declarations,
real heap snapshot/root allocation, amortized byte hashing, list/release and
following complete withdrawal/final phase. -/
theorem State.transaction_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source transactionScope=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+3 := by
  have fields := data.transaction_data
  let firstState := bind source "txs" (VarList.decodedArray array size)
  let secondState := bind firstState "ntx" (BitVec.ofNat 64 (VarList.decodedCount input start size))
  have next : State input firstState blob record array ch cursor chunk out zeros length start size := data.bound "txs" (VarList.decodedArray array size) (by decide)
  have finalState : State input secondState blob record array ch cursor chunk out zeros length start size := next.bound "ntx" (BitVec.ofNat 64 (VarList.decodedCount input start size)) (by decide)
  have pointer : secondState.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))) :=
    (bind_lookup_other firstState "ntx" "txs" (BitVec.ofNat 64 (VarList.decodedCount input start size)) (by decide)).trans (bind_lookup_same source "txs" (VarList.decodedArray array size))
  have count : secondState.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))) :=
    bind_lookup_same firstState "ntx" (BitVec.ofNat 64 (VarList.decodedCount input start size))
  let output := evaluateHOLFiniteState secondState afterNtx
  have inner := ScalarScope.declare_execute firstState output.2 "ntx" (fieldExpression 40) (BitVec.ofNat 64 (VarList.decodedCount input start size)) afterNtx output.1 next.transaction_data.2.1 rfl
  have innerRun : evaluateHOLFiniteState firstState afterTxs=(output.1,restore firstState "ntx" output.2) := by
    rw [transaction_shapes.2.1]
    exact inner
  have whole := ScalarScope.declare_execute source (restore firstState "ntx" output.2) "txs" (fieldExpression 32) (VarList.decodedArray array size) afterTxs output.1 fields.1 innerRun
  rw [←transaction_shapes.1] at whole
  have resultEq : result=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have clockEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.clock) (actual.symm.trans whole)
  change post.clock=output.2.clock at clockEq
  have observed : output.1≠some .timeOut := by rw [←resultEq]; exact notTimeout
  have paid := finalState.transaction_after_ntx_cost (post:=output.2) pointer count output.1 rfl observed
  change source.clock-output.2.clock≤transactionTailPrice input length start size+3 at paid
  rw [clockEq]
  exact paid

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_after_ntx_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_cost

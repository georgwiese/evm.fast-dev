import InitECandidate.Solver.Input.CurrentHash.PayloadPrefixCost
import InitECandidate.Solver.Input.CurrentHash.PayloadAllocation

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array cursor chunk out zeros : BitVec 64} {length start size : Nat}

def bodyPrice (input : Guest.InputBlob) (length start size : Nat) := transactionTailPrice input length start size+2028

theorem Before.after_mark_cost (data : Before input source blob record array cursor chunk out zeros length start size)
    (raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤transactionTailPrice input length start size+2027 := by
  rw [entry_shapes.2.2] at actual
  have paid := AllocationScopeCost.cost source post cursor 608#64 data.context.installed data.context.heap data.context.heapBound "ch"
    [.panop .mul [.const 19#64,.const 32#64]] afterChunks (transactionTailPrice input length start size+2025) rfl
    (by intro target room same observed final evaluated noTimeout
        have next := data.allocated raw room same
        have paid := next.prefix_cost (post:=final) observed evaluated noTimeout
        exact paid) result actual notTimeout
  have arithmetic : ∀ k : Nat,(k+2025)+2≤k+2027 := by intro k; omega
  exact Nat.le_trans paid (arithmetic _)

theorem Before.after_raw_cost (data : Before input source blob record array cursor chunk out zeros length start size)
    (raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterRaw=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice input length start size := by
  rw [entry_shapes.2.1] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark data.context.heap
    (HeapScope.mark_original_code source.code data.context.installed) result actual notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have next : Before input entry blob record array cursor chunk out zeros length start size := (data.at_clock (source.clock-1)).bound "mark" cursor (by decide)
  have pointer : entry.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))) :=
    (bind_lookup_other {source with clock:=source.clock-1} "mark" "raw" cursor (by decide)).trans raw
  have paid := next.after_mark_cost (post:=inner) pointer result remaining notTimeout
  change source.clock-1-inner.clock≤transactionTailPrice input length start size+2027 at paid
  rw [endpoint]
  change source.clock-inner.clock≤bodyPrice input length start size
  unfold bodyPrice
  omega

/-- Complete unchanged current htr_payload body source-clock bound. Physical
entry facts come from the same decoded input and real caller frontier. Actual
normal allocation/call prefixes supply every later image/heap obligation;
observed non-timeout allocation failures and other stops remain in the bound. -/
theorem body_cost (data : Before input source blob record array cursor chunk out zeros length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice input length start size := by
  let entry := bind source "raw" (blob+62#64)
  have next : Before input entry blob record array cursor chunk out zeros length start size := data.bound "raw" (blob+62#64) (by decide)
  let output := evaluateHOLFiniteState entry afterRaw
  have whole := ScalarScope.declare_execute source output.2 "raw" (fieldExpression 0) (blob+62#64) afterRaw output.1 data.raw_read rfl
  rw [←entry_shapes.1] at whole
  have resultEq : result=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have clockEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.clock) (actual.symm.trans whole)
  change post.clock=output.2.clock at clockEq
  have observed : output.1≠some .timeOut := by rw [←resultEq]; exact notTimeout
  have paid := next.after_raw_cost (post:=output.2) (bind_lookup_same source "raw" (blob+62#64)) output.1 rfl observed
  change source.clock-output.2.clock≤bodyPrice input length start size at paid
  rw [clockEq]
  exact paid

theorem body_price_expand (input : Guest.InputBlob) (length start size : Nat) :
    bodyPrice input length start size=5*transactionBytes input start size+3391*VarList.decodedCount input start size+
      848*withdrawalCount input+5*balanceLength input length+16695 := by
  unfold bodyPrice transactionTailPrice
  omega

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.after_raw_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.body_price_expand

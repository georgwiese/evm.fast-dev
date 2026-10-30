import InitECandidate.Solver.Rlp.CurrentItemTotalMemory
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Rlp.CurrentItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "rlp_item_total") expressions continuation)).2.clock≤28*length.toNat+30+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") ItemTotal.body .one pointer length (ItemTotal.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  exact ClockCost.scoped_current source name .one (ofString "rlp_item_total") expressions (Header.values pointer length) ItemTotal.body continuation callee .one
    (28*length.toNat+30) tailPrice args called paid tail

/-- Each actual continuing call supplies its returned item size, paid clock,
runtime metadata and protected memory. Its real callee state is retained. -/
theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_item_total") expressions continuation)=(none,post)) :
    ∃ word : BitVec 64,∃ paid : Nat,∃ calleePost inner,
      1≤word.toNat ∧ word.toNat≤length.toNat ∧ 1≤paid ∧ paid≤28*word.toNat+31 ∧ paid≤source.clock ∧
      calleePost.clock=source.clock-paid ∧ MemoryMetadata.erase calleePost=MemoryMetadata.erase source ∧
      Validation.Outside source calleePost 2952790016 2965299200 ∧
      evaluateHOLFiniteState (bind {calleePost with locals:=source.locals} name word) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") ItemTotal.body .one pointer length (ItemTotal.original_code source.code arena.code)
  obtain ⟨funded,target,value,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_none source post name .one (ofString "rlp_item_total") expressions (Header.values pointer length)
    ItemTotal.body continuation callee .one args called normal
  obtain ⟨word,valueEq,positive,bounded,metadata,outside,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value bodyRun
  have forward := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) ItemTotal.body
  rw [bodyRun] at forward
  change target.clock≤source.clock-1 at forward
  change source.clock-1-target.clock≤28*word.toNat+30 at price
  let paid := source.clock-target.clock
  have clock : target.clock=source.clock-paid := by dsimp [paid]; omega
  rw [valueEq] at remaining
  refine ⟨word,paid,target,inner,positive,bounded,(by dsimp [paid]; omega),
    (by dsimp [paid]; omega),Nat.sub_le _ _,clock,metadata,?_,remaining,endpoint⟩
  exact ⟨outside.runtime,fun query outsideQuery=>outside query outsideQuery⟩

end InitECandidate.Solver.Rlp.CurrentItemTotal

#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.scoped_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.scoped_none

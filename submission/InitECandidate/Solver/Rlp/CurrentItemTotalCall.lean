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
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "rlp_item_total") expressions continuation)).2.clock≤14*length.toNat+30+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") ItemTotal.body .one pointer length (ItemTotal.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  exact ClockCost.scoped_current source name .one (ofString "rlp_item_total") expressions (Header.values pointer length) ItemTotal.body continuation callee .one
    (14*length.toNat+30) tailPrice args called paid tail

/-- A real item-total call supplies its actual byte advance and cost at those
consumed bytes, together with its exact caller/clock state after return. -/
theorem callee_resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (pointerLocal : callee.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : callee.lookup (ofString "len")=some (.val (.word length)))
    (funded : 1≤source.clock) (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) ItemTotal.body=(some (.returned value),target)) :
    ∃ word : BitVec 64,∃ paid : Nat,value=.val (.word word) ∧ 1≤word.toNat ∧ word.toNat≤length.toNat ∧
      1≤paid ∧ paid≤14*word.toNat+31 ∧ paid≤source.clock ∧
      ∀ name,CallNormal.continuationEntry source target name value=bind {source with clock:=source.clock-paid} name word := by
  obtain ⟨word,valueEq,positive,bounded,frame,price⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value normal
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) ItemTotal.body
  rw [normal] at forward
  change target.clock≤source.clock-1 at forward
  change source.clock-1-target.clock≤14*word.toNat+30 at price
  let paid:=source.clock-target.clock
  have clock : source.clock-paid=target.clock := by dsimp [paid]; omega
  refine ⟨word,paid,valueEq,positive,bounded,(by dsimp [paid]; omega),(by dsimp [paid]; omega),Nat.sub_le _ _,?_⟩
  intro name
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  unfold CallNormal.continuationEntry
  rw [callerFrame,clock,valueEq]
  rfl

/-- Each actual continuing list step gets its own real item byte advance and
canonical resumed caller. No separately supplied successful parse is used. -/
theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_item_total") expressions continuation)=(none,post)) :
    ∃ word : BitVec 64,∃ paid : Nat,∃ inner,
      1≤word.toNat ∧ word.toNat≤length.toNat ∧ 1≤paid ∧ paid≤14*word.toNat+31 ∧ paid≤source.clock ∧
      evaluateHOLFiniteState (bind {source with clock:=source.clock-paid} name word) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") ItemTotal.body .one pointer length (ItemTotal.original_code source.code arena.code)
  obtain ⟨funded,target,value,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_none source post name .one (ofString "rlp_item_total") expressions (Header.values pointer length)
    ItemTotal.body continuation callee .one args called normal
  obtain ⟨word,paid,valueEq,positive,bounded,minimum,maximum,spent,canonical⟩ := callee_resume source target pointer length callee pointerLocal lengthLocal funded arena fits value bodyRun
  rw [canonical name] at remaining
  exact ⟨word,paid,inner,positive,bounded,minimum,maximum,spent,remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentItemTotal

#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.scoped_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.callee_resume
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.scoped_none

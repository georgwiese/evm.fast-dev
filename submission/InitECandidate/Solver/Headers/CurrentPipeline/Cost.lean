import InitECandidate.Solver.Headers.CurrentPipeline.Normal
import InitECandidate.Solver.Headers.CurrentPipeline.PriceRows
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual outcome of the finite original field pipeline has a
row-sensitive source-clock bound. Only reached normal prefixes supply
the current physical/type invariant used by their genuine suffix. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : State source pointer array header current bytes items active)
    (valid : Valid items.length current active code) :
    source.clock-(evaluateHOLFiniteState source (program code)).2.clock≤price items current code := by
  induction code generalizing source active with
  | done=>exact Input.ClockCost.skip source.code source rfl
  | returned=>exact Input.ClockCost.returned source.code _ source rfl
  | store offset value rest ih=>
    rw [store_step]
    have front:=Input.ClockCost.store source.code (storeAddress offset) value.expression source rfl
    have total:=Input.ClockCost.sequence_reached_current source (storeProgram offset value) (program rest) 0 (price items current rest) front (by
      intro middle normal
      have next:=state.store_normal source middle pointer array header current bytes items active offset value valid.1 valid.2.1 normal
      exact ih middle active next valid.2.2)
    simpa only [price,Nat.zero_add] using total
  | assign slot kind index control rest ih=>
    rw [assign_step]
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    have front:=CurrentHelpers.call_cost source kind array pointer control bytes index items item state.slices selected (some (some slot.name)) _ args
    have total:=Input.ClockCost.sequence_reached_current source (assigned slot kind index control) (program rest) (CurrentHelpers.bodyPrice kind item.total.toNat+1) (price items current rest) front (by
      intro middle normal
      have next:=normal_frame source middle pointer array header current bytes items active (.assign slot kind index control .done) state
        ⟨valid.1,valid.2.1,valid.2.2.1,True.intro⟩ normal
      exact ih middle active next valid.2.2.2)
    simpa only [price,rowBytes_selected items index item selected] using total
  | declare slot kind index control rest ih=>
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    obtain ⟨result,post,run⟩ : ∃ result post,evaluateHOLFiniteState source (program (.declare slot kind index control rest))=(result,post) :=
      ⟨_,_,rfl⟩
    rw [run]
    have called : evaluateHOLFiniteState source (.decCall (ofString slot.text) kind.resultShape kind.name (arguments kind index control) (program rest))=(result,post) := by
      simpa only [program,slot.of_text,valid.1] using run
    rcases CurrentHelpers.scoped_trace source post kind array pointer control bytes index items item state.slices selected slot.text _ (program rest) args result called with stopped|reached
    · simpa only [price,rowBytes_selected items index item selected] using Nat.le_trans stopped (Nat.le_add_right _ (price items current rest))
    · obtain ⟨target,value,inner,returned,shape,continued,postEq⟩ := reached
      have next:=state.resume kind returned slot value (shape.trans valid.1)
      have tailCost:=ih _ (slot::active) next valid.2.2
      rw [continued] at tailCost
      have tailClock:=evaluateHOLFiniteState_clock_le (Input.CallNormal.continuationEntry source target slot.text value) (program rest)
      rw [continued] at tailClock
      have finalClock : post.clock=inner.clock := by rw [postEq]; rfl
      have before : (Input.CallNormal.continuationEntry source target slot.text value).clock=target.clock := rfl
      change (Input.CallNormal.continuationEntry source target slot.text value).clock-inner.clock≤_ at tailCost
      change inner.clock≤(Input.CallNormal.continuationEntry source target slot.text value).clock at tailClock
      rw [before] at tailCost tailClock
      have paid:=returned.cost
      have forward:=returned.forward
      simp only [price,rowBytes_selected items index item selected]
      rw [finalClock]
      omega
  | guard slot maximum error rest ih=>
    have front : source.clock-(evaluateHOLFiniteState source (guardProgram slot maximum error)).2.clock≤0 :=
      Input.ClockCost.conditional source.code _ _ _ 0 0 (Input.ClockCost.raised source.code _ _) (Input.ClockCost.skip source.code) source rfl
    have total:=Input.ClockCost.sequence_reached_current source (guardProgram slot maximum error) (program rest) 0 (price items current rest) front (by
      intro middle normal
      have info:=(guard_pure slot maximum error).summary source
      rw [normal] at info
      have same : middle=source := info.1 rfl
      subst middle
      exact ih source active state valid)
    simpa only [program,guardProgram,price,Nat.zero_add] using total
  | choose yes no rest yesIH noIH restIH=>
    let chosen:=if current=0#64 then no else yes
    have chosenValid : Valid items.length current active chosen := by
      by_cases zero : current=0#64
      · simpa only [chosen,if_pos zero] using valid.1
      · simpa only [chosen,if_neg zero] using valid.1
    have front : source.clock-(evaluateHOLFiniteState source (program chosen)).2.clock≤price items current chosen := by
      by_cases zero : current=0#64
      · simpa only [chosen,if_pos zero] using noIH source active state (by simpa only [chosen,if_pos zero] using chosenValid)
      · simpa only [chosen,if_neg zero] using yesIH source active state (by simpa only [chosen,if_neg zero] using chosenValid)
    have total:=Input.ClockCost.sequence_reached_current source (program chosen) (program rest) (price items current chosen) (price items current rest) front (by
      intro middle normal
      have next : State middle pointer array header current bytes items active := by
        by_cases zero : current=0#64
        · exact normal_frame source middle pointer array header current bytes items active no state (by simpa only [chosen,if_pos zero] using chosenValid) (by simpa only [chosen,if_pos zero] using normal)
        · exact normal_frame source middle pointer array header current bytes items active yes state (by simpa only [chosen,if_neg zero] using chosenValid) (by simpa only [chosen,if_neg zero] using normal)
      exact restIH middle active next valid.2)
    have evaluated : evaluateHOLFiniteState source (program (.choose yes no rest))=evaluateHOLFiniteState source (.seq (program chosen) (program rest)) := by
      simp only [program,evaluateHOLFiniteState_seq_line780,choice_step source current state.currentCell,chosen]
    rw [evaluated]
    simpa only [price,chosen,apply_ite (price items current)] using total

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.cost

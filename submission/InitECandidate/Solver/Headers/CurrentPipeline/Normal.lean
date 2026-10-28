import InitECandidate.Solver.Headers.PipelineSteps
import InitECandidate.Solver.Headers.CurrentPipeline.Scope
import InitECandidate.Solver.Headers.CurrentPipeline.Store
import InitECandidate.Solver.Headers.CurrentPipeline.Assigned

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine fallthrough of any valid fragment retains the current
input, slice array, output allocation, heap, branch and active local types.
Early exits require no hypothetical continuation state. -/
theorem normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : State source pointer array header current bytes items active)
    (valid : Valid items.length current active code)
    (normal : evaluateHOLFiniteState source (program code)=(none,post)) :
    State post pointer array header current bytes items active := by
  induction code generalizing source post active with
  | done=>
    have same : source=post := by simpa [program,evaluateHOLFiniteState_skip] using normal
    exact same ▸ state
  | returned=>
    simp [program,evaluateHOLFiniteState_return,evalHOLExact,toExact,state.headerCell,shapeOfHOLExact,sizeOfShapeWithContextHOL] at normal
  | store offset value rest ih=>
    rw [store_step] at normal
    obtain ⟨middle,front,back⟩ := Input.sequence_none source post _ _ normal
    have next:=state.store_normal source middle pointer array header current bytes items active offset value valid.1 valid.2.1 front
    exact ih middle post active next valid.2.2 back
  | declare slot kind index control rest ih=>
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    have called : evaluateHOLFiniteState source (.decCall (ofString slot.text) kind.resultShape kind.name (arguments kind index control) (program rest))=(none,post) := by
      simpa only [program,slot.of_text,valid.1] using normal
    obtain ⟨target,value,inner,returned,shape,continued,postEq⟩ := CurrentHelpers.scoped_none source post kind array pointer control bytes index items item state.slices selected slot.text _ (program rest) args called
    have next:=state.resume kind returned slot value (shape.trans valid.1)
    have finalState:=ih _ inner (slot::active) next valid.2.2 continued
    rw [postEq]
    exact State.restore source inner pointer array header current bytes items slot active state finalState
  | assign slot kind index control rest ih=>
    rw [assign_step] at normal
    obtain ⟨middle,front,back⟩ := Input.sequence_none source post _ _ normal
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    have called : evaluateHOLFiniteState source (.call (some (some (.local,ofString slot.text),none)) kind.name (arguments kind index control))=(none,middle) := by
      simpa only [assigned,slot.of_text] using front
    have next:=state.assigned source middle pointer array header current control bytes index items active slot kind item selected valid.1 (arguments kind index control) args (by simpa only [slot.of_text] using called)
    exact ih middle post active next valid.2.2.2 back
  | guard slot maximum error rest ih=>
    obtain ⟨middle,front,back⟩ := Input.sequence_none source post _ _ normal
    have same : middle=source := by
      have info:=(guard_pure slot maximum error).summary source
      change evaluateHOLFiniteState source (guardProgram slot maximum error)=(none,middle) at front
      rw [front] at info
      exact info.1 rfl
    subst middle
    exact ih source post active state valid back
  | choose yes no rest yesIH noIH restIH=>
    obtain ⟨middle,front,back⟩ := Input.sequence_none source post _ _ normal
    rw [choice_step source current state.currentCell] at front
    have next : State middle pointer array header current bytes items active := by
      by_cases zero : current=0#64
      · rw [if_pos zero] at front
        exact noIH source middle active state (by simpa only [Valid,if_pos zero] using valid.1) front
      · rw [if_neg zero] at front
        exact yesIH source middle active state (by simpa only [Valid,if_neg zero] using valid.1) front
    exact restIH middle post active next valid.2 back

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.normal_frame

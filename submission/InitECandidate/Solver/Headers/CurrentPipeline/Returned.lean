import InitECandidate.Solver.Headers.CurrentPipeline.Normal
import InitECandidate.Solver.Headers.CurrentHelpers.Returned
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every genuine return comes from the original return-h leaf and a real
current field state. Erasing only locals/clock accounts for lexical exits;
memory, globals, oracle and all immutable metadata remain exact. -/
theorem returned_state (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : State source pointer array header current bytes items active)
    (valid : Valid items.length current active code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program code)=(some (.returned value),post)) :
    value=.val (.word header) ∧ ∃ finish finalActive,
      State finish pointer array header current bytes items finalActive ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase finish := by
  induction code generalizing source post active with
  | done=>simp [program,evaluateHOLFiniteState_skip] at normal
  | returned=>
    obtain ⟨read,postEq⟩ := Input.return_normal source post _ value normal
    have actual : eval source (.var .local (ofString "h"))=some (.val (.word header)) := by simp [eval,evalHOLExact,toExact,state.headerCell]
    have valueEq : value=.val (.word header) := Option.some.inj (read.symm.trans actual)
    exact ⟨valueEq,source,active,state,by rw [postEq]; rfl⟩
  | store offset stored rest ih=>
    rw [store_step] at normal
    have never:=(Input.LocalPrefix.store (key:=ofString "arr") (storeAddress offset) stored.expression).summary source |>.2
    obtain ⟨middle,front,back⟩ := Input.sequence_returned source post _ _ value never normal
    have next:=state.store_normal source middle pointer array header current bytes items active offset stored valid.1 valid.2.1 front
    exact ih middle post active next valid.2.2 back
  | assign slot kind index control rest ih=>
    rw [assign_step] at normal
    have safe : Input.LocalPrefix (ofString "arr") (assigned slot kind index control) :=
      .call (some slot.name) kind.name _ (by intro name same; have equal:=Option.some.inj same; subst name; exact Ne.symm slot.not_array)
    obtain ⟨middle,front,back⟩ := Input.sequence_returned source post _ _ value (safe.summary source).2 normal
    have next:=normal_frame source middle pointer array header current bytes items active (.assign slot kind index control .done) state
      ⟨valid.1,valid.2.1,valid.2.2.1,True.intro⟩ front
    exact ih middle post active next valid.2.2.2 back
  | declare slot kind index control rest ih=>
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    have called : evaluateHOLFiniteState source (.decCall (ofString slot.text) kind.resultShape kind.name (arguments kind index control) (program rest))=(some (.returned value),post) := by
      simpa only [program,slot.of_text,valid.1] using normal
    obtain ⟨target,returned,inner,real,shape,continued,postEq⟩ := CurrentHelpers.scoped_returned source post kind array pointer control bytes index items item state.slices selected slot.text _ (program rest) args value called
    have next:=state.resume kind real slot returned (shape.trans valid.1)
    obtain ⟨valueEq,finish,finalActive,finalState,erased⟩ := ih _ inner (slot::active) next valid.2.2 continued
    exact ⟨valueEq,finish,finalActive,finalState,by rw [postEq]; exact erased⟩
  | guard slot maximum error rest ih=>
    obtain ⟨middle,front,back⟩ := Input.sequence_returned source post _ _ value ((guard_pure slot maximum error).summary source).2 normal
    change evaluateHOLFiniteState source (guardProgram slot maximum error)=(none,middle) at front
    have info:=(guard_pure slot maximum error).summary source
    rw [front] at info
    have same : middle=source := info.1 rfl
    subst middle
    exact ih source post active state valid back
  | choose yes no rest yesIH noIH restIH=>
    rw [program,evaluateHOLFiniteState_seq_line780,choice_step source current state.currentCell] at normal
    let chosen:=if current=0#64 then no else yes
    have chosenValid : Valid items.length current active chosen := by
      by_cases zero : current=0#64
      · simpa only [chosen,if_pos zero] using valid.1
      · simpa only [chosen,if_neg zero] using valid.1
    have runChosen := normal
    generalize firstRun : evaluateHOLFiniteState source (program (if current=0#64 then no else yes))=output at runChosen
    obtain ⟨firstResult,middle⟩ := output
    cases firstResult with
    | none=>
      have next:=normal_frame source middle pointer array header current bytes items active chosen state chosenValid firstRun
      exact restIH middle post active next valid.2 runChosen
    | some result=>
      have same : result=.returned value := Option.some.inj (congrArg Prod.fst runChosen)
      have endpoint : middle=post := congrArg Prod.snd runChosen
      subst result
      subst middle
      by_cases zero : current=0#64
      · exact noIH source post active state (by simpa only [chosen,if_pos zero] using chosenValid) (by simpa only [chosen,if_pos zero] using firstRun)
      · exact yesIH source post active state (by simpa only [chosen,if_neg zero] using chosenValid) (by simpa only [chosen,if_neg zero] using firstRun)

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.returned_state

import InitECandidate.Solver.Headers.PipelineReturned
import InitECandidate.Solver.Headers.FieldMemory

namespace InitECandidate.Solver.Headers.Pipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Ordinary (result : Option (PanSemResultExact 64)) : Prop := result=none ∨ ∃ value,result=some (.returned value)

private theorem ordinary_sequence (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (ordinary : Ordinary result)
    (never : ∀ value,(evaluateHOLFiniteState source first).1≠some (.returned value))
    (run : evaluateHOLFiniteState source (.seq first second)=(result,post)) :
    ∃ middle,evaluateHOLFiniteState source first=(none,middle) ∧ evaluateHOLFiniteState middle second=(result,post) := by
  rcases ordinary with rfl|⟨value,rfl⟩
  · exact Input.sequence_none source post first second run
  · exact Input.sequence_returned source post first second value never run

structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (header : BitVec 64) : Prop where
  memory : FieldMemory source target cutoff header
  globals : ∀ key,target.globals.lookup key=source.globals.lookup key

theorem Frame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (header : BitVec 64)
    (first : Frame source middle cutoff header) (second : Frame middle target cutoff header) : Frame source target cutoff header :=
  ⟨FieldMemory.trans source middle target cutoff header first.memory second.memory,fun key=>(second.globals key).trans (first.globals key)⟩

/-- The full real field pipeline protects all ordinary words between its
incoming scratch boundary and fresh header, including prior witness data
and earlier headers. Normal returns and fallthroughs both carry this frame. -/
theorem normal_frame_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (valid : Valid items.length current active code) (result : Option (PanSemResultExact 64)) (ordinary : Ordinary result)
    (normal : evaluateHOLFiniteState source (program code)=(result,post)) : Frame source post cutoff header := by
  induction code generalizing source post active result with
  | done=>
    have frame:=Input.LocalEffects.skip source.code source rfl
    simp only [program] at normal
    rw [normal] at frame
    exact ⟨fun query _ _=>congrFun (Input.LocalEffects.memory_of_erase source post frame) query,fun key=>congrArg (fun state=>state.globals.lookup key) frame⟩
  | returned=>
    have frame:=Input.LocalEffects.returned source.code (.var .local (ofString "h")) source rfl
    simp only [program] at normal
    rw [normal] at frame
    exact ⟨fun query _ _=>congrFun (Input.LocalEffects.memory_of_erase source post frame) query,fun key=>congrArg (fun state=>state.globals.lookup key) frame⟩
  | store offset value rest ih=>
    rw [store_step] at normal
    have never:=(Input.LocalPrefix.store (key:=ofString "arr") (storeAddress offset) value.expression).summary source |>.2
    obtain ⟨middle,front,back⟩ := ordinary_sequence source post _ _ result ordinary never normal
    have next:=state.store_normal source middle pointer array header cursor limit current bytes cutoff items active offset value valid.1 valid.2.1 front
    exact Frame.trans source middle post cutoff header
      ⟨state.store_memory source middle pointer array header cursor limit current bytes cutoff items active offset value valid.1 valid.2.1 front,
        by intro key; rw [Input.store_none_frame source middle (storeAddress offset) value.expression front]⟩
      (ih middle post active next valid.2.2 result ordinary back)
  | assign slot kind index control rest ih=>
    rw [assign_step] at normal
    have safe : Input.LocalPrefix (ofString "arr") (assigned slot kind index control) :=
      .call (some slot.name) kind.name _ (by intro name same; have equal:=Option.some.inj same; subst name; exact Ne.symm slot.not_array)
    obtain ⟨middle,front,back⟩ := ordinary_sequence source post _ _ result ordinary (safe.summary source).2 normal
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have called : evaluateHOLFiniteState source (.call (some (some (.local,ofString slot.text),none)) kind.name (arguments kind index control))=(none,middle) := by simpa only [assigned,slot.of_text] using front
    obtain ⟨target,value,real,shape,middleEq⟩ := Helper.assigned_normal source middle kind array pointer cursor limit control bytes cutoff index items item state.slices selected slot.text _ (arguments_read source array state.arrayCell kind index control) state.code called
    have next:=normal_frame source middle pointer array header cursor limit current bytes cutoff items active (.assign slot kind index control .done) state ⟨valid.1,valid.2.1,valid.2.2.1,True.intro⟩ front
    have frontMemory : FieldMemory source middle cutoff header := by
      intro query lower upper
      rw [middleEq]
      exact real.above query (state.slices.scratchBelow.trans lower)
    exact Frame.trans source middle post cutoff header ⟨frontMemory,by intro key; rw [middleEq]; exact real.globals key⟩ (ih middle post active next valid.2.2.2 result ordinary back)
  | declare slot kind index control rest ih=>
    let item:=items[index]'valid.2.1
    have selected : items[index]?=some item := by simp [item,valid.2.1]
    have args:=arguments_read source array state.arrayCell kind index control
    have called : evaluateHOLFiniteState source (.decCall (ofString slot.text) kind.resultShape kind.name (arguments kind index control) (program rest))=(result,post) := by simpa only [program,slot.of_text,valid.1] using normal
    have reached : ∃ target value inner,Helper.Returned source target kind array pointer cursor limit bytes cutoff item.total.toNat items ∧ shapeOfHOLExact value=kind.resultShape ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target slot.text value) (program rest)=(result,inner) ∧ post=restore source slot.text inner := by
      rcases ordinary with rfl|⟨value,rfl⟩
      · exact Helper.scoped_normal source post kind array pointer cursor limit control bytes cutoff index items item state.slices selected slot.text _ (program rest) args state.code called
      · exact Helper.scoped_returned source post kind array pointer cursor limit control bytes cutoff index items item state.slices selected slot.text _ (program rest) args state.code value called
    obtain ⟨target,value,inner,real,shape,continued,postEq⟩ := reached
    have next:=state.resume source target kind pointer array header cursor limit current bytes cutoff item.total.toNat items active real slot value (shape.trans valid.1)
    have back:=ih _ inner (slot::active) next valid.2.2 result ordinary continued
    constructor
    · intro query lower upper
      rw [postEq]
      exact (back.memory query lower upper).trans (real.above query (state.slices.scratchBelow.trans lower))
    · intro key
      rw [postEq]
      exact (back.globals key).trans (real.globals key)
  | guard slot maximum error rest ih=>
    obtain ⟨middle,front,back⟩ := ordinary_sequence source post _ _ result ordinary ((guard_pure slot maximum error).summary source).2 normal
    change evaluateHOLFiniteState source (guardProgram slot maximum error)=(none,middle) at front
    have info:=(guard_pure slot maximum error).summary source
    rw [front] at info
    have same : middle=source := info.1 rfl
    subst middle
    exact ih source post active state valid result ordinary back
  | choose yes no rest yesIH noIH restIH=>
    rw [program,evaluateHOLFiniteState_seq_line780,choice_step source current state.currentCell] at normal
    let chosen:=if current=0#64 then no else yes
    have chosenValid : Valid items.length current active chosen := by
      by_cases zero : current=0#64
      · simpa only [chosen,if_pos zero] using valid.1
      · simpa only [chosen,if_neg zero] using valid.1
    have chosenIH (middle : PanSemStateFiniteExact 64 Guest.HostMemory) (observation : Option (PanSemResultExact 64)) (controlResult : Ordinary observation)
        (run : evaluateHOLFiniteState source (program chosen)=(observation,middle)) : Frame source middle cutoff header := by
      by_cases zero : current=0#64
      · exact noIH source middle active state (by simpa only [chosen,if_pos zero] using chosenValid) observation controlResult (by simpa only [chosen,if_pos zero] using run)
      · exact yesIH source middle active state (by simpa only [chosen,if_neg zero] using chosenValid) observation controlResult (by simpa only [chosen,if_neg zero] using run)
    generalize firstRun : evaluateHOLFiniteState source (program (if current=0#64 then no else yes))=output at normal
    obtain ⟨firstResult,middle⟩ := output
    cases firstResult with
    | none=>
      have next:=normal_frame source middle pointer array header cursor limit current bytes cutoff items active chosen state chosenValid firstRun
      exact Frame.trans source middle post cutoff header (chosenIH middle none (Or.inl rfl) firstRun) (restIH middle post active next valid.2 result ordinary normal)
    | some firstResult=>
      have same : some firstResult=result := congrArg Prod.fst normal
      have endpoint : middle=post := congrArg Prod.snd normal
      subst middle
      exact chosenIH post (some firstResult) (same.symm ▸ ordinary) firstRun

theorem memory_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (valid : Valid items.length current active code) (result : Option (PanSemResultExact 64)) (ordinary : Ordinary result)
    (normal : evaluateHOLFiniteState source (program code)=(result,post)) : FieldMemory source post cutoff header :=
  (normal_frame_data source post pointer array header cursor limit current bytes cutoff items active code state valid result ordinary normal).memory

theorem globals_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (code : Code) (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (valid : Valid items.length current active code) (result : Option (PanSemResultExact 64)) (ordinary : Ordinary result)
    (normal : evaluateHOLFiniteState source (program code)=(result,post)) : ∀ key,post.globals.lookup key=source.globals.lookup key :=
  (normal_frame_data source post pointer array header cursor limit current bytes cutoff items active code state valid result ordinary normal).globals

end InitECandidate.Solver.Headers.Pipeline

#print axioms InitECandidate.Solver.Headers.Pipeline.memory_frame

#print axioms InitECandidate.Solver.Headers.Pipeline.normal_frame_data
#print axioms InitECandidate.Solver.Headers.Pipeline.globals_frame

import InitECandidate.Solver.Input.HeapMarkTrace
import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.SavedHeapReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def release (saved : String) : ProgHOL 64 := .seq
  (.call (some (none,none)) (ofString "heap_release") [localVar saved]) (.return (.const 0#64))

theorem release_body (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64)
    (binding : source.locals.lookup (ofString "m") = some (.val (.word mark))) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source HeapScope.releaseBody = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  classical
  rw [HeapScope.release_shape] at actual
  have safe : LocalPrefix (ofString "m") (.assign .global (ofString "heap_ptr") (localVar "m")) := .globalAssign _ _
  obtain ⟨middle,assigned,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : eval source (localVar "m") = some (.val (.word mark)) := by
    simpa [eval,evalHOLExact,toExact,localVar] using binding
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign,read] at assigned
  simp only at assigned
  split at assigned
  · have endpoint : middle = setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) source := (congrArg Prod.snd assigned).symm
    have unchanged := GlobalEffects.returned (ofString "heap_ptr") middle.code (.const 0#64) middle rfl
    rw [returned] at unchanged
    exact (congrArg Prod.snd unchanged).trans (by rw [endpoint]; simp [GlobalEffects.erase,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  · cases assigned

theorem release_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : String) (mark : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString saved) = some (.val (.word mark)))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar saved]) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar saved] = some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,binding]
  obtain ⟨callee,called,m⟩ := CallNormal.unary_environment source.code.lookup (ofString "heap_release") "m" HeapScope.releaseBody mark
    (HeapScope.release_original_code source.code installed)
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "heap_release") [localVar saved] actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have same := Option.some.inj (actualCalled.symm.trans called)
  cases same
  have result := release_body (callEntryStateHOLFinite source callee) target mark m value bodyRun
  rw [endpoint]
  exact result

/-- A real final release, with no premise about the previous heap cell.
Its actual normal assignment supplies every shape/validity fact it needs. -/
theorem release_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : String) (mark : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString saved) = some (.val (.word mark))) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (release saved) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString saved) (.call (some (none,none)) (ofString "heap_release") [localVar saved]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have restored := release_call source middle saved mark installed binding normal
  have unchanged := GlobalEffects.returned (ofString "heap_ptr") middle.code (.const 0#64) middle rfl
  rw [returned] at unchanged
  exact (congrArg Prod.snd unchanged).trans restored

/-- A structural saved-mark suffix. Earlier callees and memory effects are
unrestricted; actual normal continuation retains the saved caller binding. -/
inductive Tail (saved : String) : ProgHOL 64 → Prop where
  | release : Tail saved (SavedHeapReturn.release saved)
  | releaseThen (rest : ProgHOL 64)
      (pure : ∀ code, OriginalCode.Installed code → GlobalEffects.Preserves (ofString "heap_ptr") code rest) :
      Tail saved (.seq (.call (some (none,none)) (ofString "heap_release") [localVar saved]) rest)
  | seq {first rest : ProgHOL 64} (safe : LocalPrefix (ofString saved) first) (ending : Tail saved rest) : Tail saved (.seq first rest)
  | dec (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) {rest : ProgHOL 64}
      (different : ofString saved ≠ ofString name) (ending : Tail saved rest) : Tail saved (.dec (ofString name) shape expression rest)
  | decCall (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) {rest : ProgHOL 64}
      (different : ofString saved ≠ ofString name) (ending : Tail saved rest) : Tail saved (.decCall (ofString name) shape function arguments rest)

theorem Tail.sound {saved : String} {program : ProgHOL 64} (certificate : Tail saved program)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString saved) = some (.val (.word mark))) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source program = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  induction certificate generalizing source post mark value with
  | release => exact release_return source post saved mark installed binding value actual
  | releaseThen rest pure =>
    have safe : LocalPrefix (ofString saved) (.call (some (none,none)) (ofString "heap_release") [localVar saved]) :=
      .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
    have restored := release_call source middle saved mark installed binding normal
    have nextCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
    have unchanged := pure middle.code nextCode middle rfl
    rw [remaining] at unchanged
    exact (congrArg Prod.snd unchanged).trans restored
  | seq safe ending ih =>
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    have nextCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
    exact ih middle post mark nextCode ((summary.1 rfl).trans binding) value remaining
  | dec name shape expression different ending ih =>
    obtain ⟨declared,inner,read,checked,normal,endpoint⟩ := CallNormal.declaration_normal_entry source post name shape expression _ value actual
    have next : (setVarHOLFinite (ofString name) declared source).locals.lookup (ofString saved) = some (.val (.word mark)) := by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using binding
    have result := ih (setVarHOLFinite (ofString name) declared source) inner mark installed next value normal
    rw [endpoint]
    exact result
  | decCall name shape function arguments different ending ih =>
    obtain ⟨calleePost,returned,inner,normal,endpoint,domain,endian,shapes,code,typed⟩ := CallNormal.normal_entry source post name shape function arguments _ value actual
    let entry := CallNormal.continuationEntry source calleePost name returned
    have next : entry.locals.lookup (ofString saved) = some (.val (.word mark)) := by
      simpa [entry,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using binding
    have nextCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed calleePost.code; rw [code]; exact installed
    have result := ih entry inner mark nextCode next value normal
    rw [endpoint]
    exact result

/-- Common ignored-call prefix: the actual callee reinstalls saved caller
locals before the same continuing suffix. -/
theorem Tail.ignored_call {saved : String} {rest : ProgHOL 64} (function : MlS) (arguments : List (ExpHOL 64))
    (ending : Tail saved rest) : Tail saved (.seq (.call (some (none,none)) function arguments) rest) :=
  .seq (.call none _ _ (by intro name impossible; cases impossible)) ending

/-- The actual heap_mark return selects the saved value for that same
continuation. Its genuine final release restores the entering heap exactly. -/
theorem marked_scope (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : String) (mark : BitVec 64)
    (continuation : ProgHOL 64) (certificate : Tail saved continuation) (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark))) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (.decCall (ofString saved) .one (ofString "heap_mark") [] continuation) = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  obtain ⟨positive,inner,normal,endpoint⟩ := HeapScope.mark_call_trace source post mark saved continuation heap
    (HeapScope.mark_original_code source.code installed) (some (.returned value)) actual (by simp)
  rw [endpoint]
  exact certificate.sound (bind {source with clock:=source.clock-1} saved mark) inner mark installed (bind_lookup_same _ _ _) value normal

end InitECandidate.Solver.Input.SavedHeapReturn

#print axioms InitECandidate.Solver.Input.SavedHeapReturn.release_body
#print axioms InitECandidate.Solver.Input.SavedHeapReturn.release_call
#print axioms InitECandidate.Solver.Input.SavedHeapReturn.release_return
#print axioms InitECandidate.Solver.Input.SavedHeapReturn.Tail.sound
#print axioms InitECandidate.Solver.Input.SavedHeapReturn.marked_scope

#print axioms InitECandidate.Solver.Input.SavedHeapReturn.Tail.ignored_call

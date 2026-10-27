import InitECandidate.Solver.Input.CurrentStartup.SeparatedInput

namespace InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual continuing main decoder prefix selects this particular
stateless run and preserves its exact physical post-state and clock. -/
theorem current {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701134640 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target) :
    ∃ origin : DecoderOrigin, MainSeparatedInput.RootRun input origin ∧
      target.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
      LocalEffects.erase target = LocalEffects.erase origin.post ∧ target.clock = origin.post.clock := by
  obtain ⟨before, setup, positive, callee, decoderPost, word, entry, cursor, called, returned, binding⟩ :=
    DecoderPrefix.decoder_entry_heap initial execution
  have lower := StartupHeap.setup_lower 2701134640 initial.arena.code heap setup
  have cell := (setup.globals (ofString "ssz_offs") (MainSeparatedInput.setup_offsets source.code initial.arena.code)).trans offsets
  obtain ⟨origin, actual, wordEq, frame, clock⟩ := MainSeparatedInput.stateless_run_root input
    (callEntryStateHOLFinite before callee) decoderPost entry lower cell word returned
  refine ⟨origin, actual, ?_, ?_, ?_⟩
  · rw [binding, wordEq]
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · have currentFrame : LocalEffects.erase target = LocalEffects.erase decoderPost := by rw [binding]; rfl
    exact currentFrame.trans frame
  · change target.clock = origin.post.clock
    rw [binding]
    exact clock

/-- Both real alternatives at main's decoder cut, with a selected run on
continuation and the original stopped observation on the other alternative. -/
def Cut (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  (∃ current inner, ∃ origin : DecoderOrigin,
    CallPrefix.Execution source DecoderPrefix.actions current ∧ ArenaState current ∧
    MainSeparatedInput.RootRun input origin ∧
    current.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
    LocalEffects.erase current = LocalEffects.erase origin.post ∧ current.clock = origin.post.clock ∧
    evaluateHOLFiniteState current DecoderPrefix.afterDecoder = (result, inner) ∧
    post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
  (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program DecoderPrefix.actions .skip) = (result, stopped) ∧
    ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧ LocalEffects.erase post = LocalEffects.erase stopped)

theorem cut (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : HostState input source)
    (heap : NormalHeapEffects.AtLeast 2701134640 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (actual : evaluateHOLFiniteState source afterStartup = (result, post)) : Cut input source result post := by
  rcases DecoderPrefix.split_execution source post result initial.arena actual with continued | stopped
  · obtain ⟨target, inner, execution, arena, suffixRun, clock, frame⟩ := continued
    obtain ⟨origin, run, si, originFrame, originClock⟩ := current initial heap offsets execution
    exact Or.inl ⟨target, inner, origin, execution, arena, run, si, originFrame, originClock, suffixRun, clock, frame⟩
  · exact Or.inr stopped

/-- A genuine complete source observation reaches this selected decoder run
or stops earlier, retaining the actual result, final FFI events and all scopes. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, middle) ∧
          HostState input middle ∧ Cut input middle result target) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, startup, classified, observation⟩ :=
    reached_host input outcome events terminates
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases startup with continued | stopped
  · obtain ⟨middle, startupRun, initial, actual⟩ := continued
    exact Or.inl ⟨middle, startupRun, initial, cut input middle target result initial
      (StartupHeap.main_lower input origin middle entry startupRun)
      (EarlyWorkspace.main_offsets input origin middle entry startupRun) actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot

#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot.current
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot.cut
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot.reached

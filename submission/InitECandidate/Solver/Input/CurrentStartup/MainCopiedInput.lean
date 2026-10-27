import InitECandidate.Solver.Input.CurrentStartup.StatelessEntry

namespace InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real stateless decoder run, with copied bytes and actual parameter
bindings. No schema, canonical offsets, gas value or future helper success
is assumed by this entry predicate. -/
def StatelessRun (input : Guest.InputBlob) (word : BitVec 64) : Prop :=
  ∃ source target pointer,
    input.length % 2^64 ≤ Guest.maxInputBytes ∧
    HostState input source ∧ HeapState source ∧
    Blob.InputBytes source input pointer (input.length % 2^64) ∧
    source.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
    source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))) ∧
    evaluateHOLFiniteState source (Code.body .decode_stateless_input) =
      (some (.returned (.val (.word word))), target)

theorem stateless_run (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source) (heap : HeapState source) (word : BitVec 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_host_input) =
      (some (.returned (.val (.word word))), target)) : StatelessRun input word := by
  obtain ⟨before, pointer, ready, callee, post, lengthBound, precheckRun, copied, entry,
    heapEntry, bytes, pCell, lenCell, returned, restored⟩ :=
    DecoderInput.stateless_reached input source target initial heap (.val (.word word)) actual
  exact ⟨callEntryStateHOLFinite ready callee, post, pointer, lengthBound, entry, heapEntry, bytes, pCell, lenCell, returned⟩

/-- A genuine completed decoder prefix or its actual stopped execution.
Both cases retain final nonlocal observation; the continuation additionally
contains a real stateless input run and main's actual si result binding. -/
def DecoderCut (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  (∃ current inner, ∃ word : BitVec 64,
    CallPrefix.Execution source DecoderPrefix.actions current ∧ ArenaState current ∧
    current.locals.lookup (ofString "si") = some (.val (.word word)) ∧ StatelessRun input word ∧
    evaluateHOLFiniteState current DecoderPrefix.afterDecoder = (result, inner) ∧
    post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
  (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program DecoderPrefix.actions .skip) = (result, stopped) ∧
    ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧ LocalEffects.erase post = LocalEffects.erase stopped)

theorem decoder_cut (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : HostState input source)
    (actual : evaluateHOLFiniteState source afterStartup = (result, post)) : DecoderCut input source result post := by
  rcases DecoderPrefix.split_execution source post result initial.arena actual with continued | stopped
  · obtain ⟨current, inner, execution, arena, actualTail, clock, frame⟩ := continued
    obtain ⟨before, setup, positive, callee, decoderPost, word, entry, heap, called, returned, binding⟩ :=
      DecoderPrefix.decoder_entry_heap initial execution
    have parsed := stateless_run input (callEntryStateHOLFinite before callee) decoderPost entry heap word returned
    refine Or.inl ⟨current, inner, word, execution, arena, ?_, parsed, actualTail, clock, frame⟩
    rw [binding]
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · exact Or.inr stopped

/-- Complete terminating source observations now expose the real copied-
input/stateless entry whenever the actual decoder prefix continues. Startup
and decoder stops remain explicit alternatives with exact original events;
there is no extra future-completion or non-timeout hypothesis. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, middle) ∧
          HostState input middle ∧ DecoderCut input middle result target) ∨
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
    exact Or.inl ⟨middle, startupRun, initial, decoder_cut input middle target result initial actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput

#print axioms InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput.stateless_run
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput.decoder_cut
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput.reached

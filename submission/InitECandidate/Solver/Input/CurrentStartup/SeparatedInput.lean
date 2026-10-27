import InitECandidate.Solver.Input.CurrentStartup.CopiedHeap
import InitECandidate.Solver.Input.CurrentStartup.StartupHeap
import InitECandidate.Solver.Input.CurrentStartup.MainCopiedInput

namespace InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual stateless entry with the copied input strictly above the real
64-byte SSZ offset workspace. This is geometry, not its later memory frame. -/
def StatelessRun (input : Guest.InputBlob) (word : BitVec 64) : Prop :=
  ∃ source target pointer,
    input.length % 2^64 ≤ Guest.maxInputBytes ∧
    HostState input source ∧ HeapState source ∧
    Blob.InputBytes source input pointer (input.length % 2^64) ∧
    source.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
    source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))) ∧
    source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    2701134640 ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 ∧
    (∀ offset : Nat, offset < 64 → 2701132528 + offset < pointer.toNat) ∧
    NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) source ∧
    evaluateHOLFiniteState source (Code.body .decode_stateless_input) =
      (some (.returned (.val (.word word))), target)

theorem setup_offsets (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (ofString "ssz_offs") code (CallPrefix.program DecoderPrefix.setupActions .skip) := by
  simp only [DecoderPrefix.setupActions, DecoderPrefix.actions_shape, List.take_succ_cons, List.take_zero, CallPrefix.program]
  refine GlobalEffects.scoped_body (ofString "ssz_offs") code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed) ?_
  refine GlobalEffects.scoped_body (ofString "ssz_offs") code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed) ?_
  refine GlobalEffects.sequence (ofString "ssz_offs") code _ _
    (GlobalEffects.call_body (ofString "ssz_offs") code (some none) (Code.name .memzero) _
      (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
      (Code.installed code installed .memzero) (OffsetsFrame.memzero code installed)) ?_
  exact GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _
    (GlobalEffects.declared (ofString "ssz_offs") code _ _ _ _ (GlobalEffects.skip (ofString "ssz_offs") code))

/-- Both the workspace cell and the input pointer lower bound come from
real preceding execution; no disjointness premise is imposed. -/
theorem stateless_run (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701134640 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))) (word : BitVec 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_host_input) =
      (some (.returned (.val (.word word))), target)) : StatelessRun input word := by
  have cursor : HeapState source := by
    obtain ⟨pointer, cell, low, high, aligned⟩ := heap
    exact ⟨pointer, cell, high, aligned⟩
  obtain ⟨before, pointer, ready, callee, post, lengthBound, precheckRun, copied, entry,
    heapEntry, bytes, pCell, lenCell, returned, restored, heapCell, globals⟩ :=
    DecoderInput.stateless_reached input source target initial cursor (.val (.word word)) actual
  obtain ⟨old, oldCell, low, high, aligned⟩ := StartupHeap.precheck_lower source before 2701134640 initial.arena.code heap precheckRun
  have same : old = pointer := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans heapCell)))
  subst old
  refine ⟨callEntryStateHOLFinite ready callee, post, pointer, lengthBound, entry, heapEntry, bytes,
    pCell, lenCell, ?_, low, aligned, copied.1, ?_, DecoderInput.copied_frontier input before ready pointer (input.length % 2^64) _ copied, returned⟩
  · exact (globals (ofString "ssz_offs") (by decide)).trans offsets
  · intro offset small
    omega

/-- A continuing real decoder prefix exposes separated input. Stopped
prefixes remain explicit, with their full nonlocal observations. -/
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
    (heap : NormalHeapEffects.AtLeast 2701134640 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (actual : evaluateHOLFiniteState source afterStartup = (result, post)) : DecoderCut input source result post := by
  rcases DecoderPrefix.split_execution source post result initial.arena actual with continued | stopped
  · obtain ⟨current, inner, execution, arena, actualTail, clock, frame⟩ := continued
    obtain ⟨before, setup, positive, callee, decoderPost, word, entry, cursor, called, returned, binding⟩ :=
      DecoderPrefix.decoder_entry_heap initial execution
    have lower := StartupHeap.setup_lower 2701134640 initial.arena.code heap setup
    have cell := (setup.globals (ofString "ssz_offs") (setup_offsets source.code initial.arena.code)).trans offsets
    have parsed := stateless_run input (callEntryStateHOLFinite before callee) decoderPost entry lower cell word returned
    refine Or.inl ⟨current, inner, word, execution, arena, ?_, parsed, actualTail, clock, frame⟩
    rw [binding]
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · exact Or.inr stopped

/-- Whole terminating source observations supply workspace/input separation
at actual stateless entry, including arbitrary mathematical input lengths. -/
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
    have lower := StartupHeap.main_lower input origin middle entry startupRun
    have offsets := EarlyWorkspace.main_offsets input origin middle entry startupRun
    exact Or.inl ⟨middle, startupRun, initial, decoder_cut input middle target result initial lower offsets actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput

#print axioms InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput.setup_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput.stateless_run
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput.decoder_cut
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainSeparatedInput.reached

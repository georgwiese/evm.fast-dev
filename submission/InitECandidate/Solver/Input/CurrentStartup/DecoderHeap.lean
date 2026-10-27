import InitECandidate.Solver.Input.CurrentStartup.AllocationCursor

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def setupTailActions : List CallPrefix.Action :=
  [.command (.call (some (none, none)) (Code.name .memzero)
      [.var .local (ofString "z32"), .const 32#64]),
    .declare (ofString "si") .one (.const 0#64),
    .declare (ofString "err_code") .one (.const 0#64)]

def setupAllocationActions : List CallPrefix.Action :=
  [.scoped (ofString "out") .one (Code.name .alloc) [.const 256#64],
    .scoped (ofString "z32") .one (Code.name .alloc) [.const 32#64]]

theorem setup_split : setupActions = setupAllocationActions ++ setupTailActions := by
  simp only [setupActions, actions_shape, setupAllocationActions, setupTailActions,
    List.take_succ_cons, List.take_zero]
  rfl

theorem setup_tail_heap (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (ofString "heap_ptr") code (CallPrefix.program setupTailActions .skip) := by
  simp only [setupTailActions, CallPrefix.program]
  refine GlobalEffects.sequence (ofString "heap_ptr") code _ _ ?_ ?_
  · exact GlobalEffects.call_body (ofString "heap_ptr") code (some none) (Code.name .memzero) _
      (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
      (Code.installed code installed .memzero) (Memzero.any_key (ofString "heap_ptr") code)
  · exact GlobalEffects.declared (ofString "heap_ptr") code _ _ _ _
      (GlobalEffects.declared (ofString "heap_ptr") code _ _ _ _ (GlobalEffects.skip (ofString "heap_ptr") code))

/-- The second real allocation bootstraps the required heap invariant.
No initial scalar heap cell, startup allocation size or room is assumed. -/
theorem setup_allocated_heap {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (installed : OriginalCode.Installed source.code)
    (execution : CallPrefix.Execution source setupAllocationActions target) : HeapState target := by
  cases execution with
  | step first next =>
    cases next with
    | step second last =>
      cases last
      have currentInstalled := installed
      rw [← first.runtime.2.2.2.1] at currentInstalled
      exact allocation_reached (ofString "z32") 32#64 currentInstalled second

/-- Main's actual setup leaves a bounded eight-byte-aligned heap cursor at
its decoder call, derived from real allocation and the untouched suffix. -/
theorem setup_heap_state {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (installed : OriginalCode.Installed source.code)
    (execution : CallPrefix.Execution source setupActions target) : HeapState target := by
  rw [setup_split] at execution
  obtain ⟨middle, allocated, tail⟩ := execution.split setupAllocationActions setupTailActions
  have cursor := setup_allocated_heap installed allocated
  have currentInstalled := installed
  rw [← allocated.runtime.2.2.2.1] at currentInstalled
  obtain ⟨pointer, heap, bound, aligned⟩ := cursor
  exact ⟨pointer, (tail.globals (ofString "heap_ptr") (setup_tail_heap _ currentInstalled)).trans heap, bound, aligned⟩

/-- A completed actual decoder prefix supplies all nonlocal input_blob
entry prerequisites at the real decode_host_input body entry. Internal
precheck/input_blob reachability still has to transport them to that call. -/
theorem decoder_entry_heap {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (execution : CallPrefix.Execution source actions target) :
    ∃ before, CallPrefix.Execution source setupActions before ∧
      1 ≤ before.clock ∧ ∃ callee post, ∃ word : BitVec 64,
      HostState input (callEntryStateHOLFinite before callee) ∧
      HeapState (callEntryStateHOLFinite before callee) ∧
      lookupCodeHOLFinite before.code.lookup (Code.name .decode_host_input) [] =
        some (Code.body .decode_host_input, callee, .one) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite before callee) (Code.body .decode_host_input) =
        (some (.returned (.val (.word word))), post) ∧
      target = setVarHOLFinite (ofString "si") (.val (.word word)) {post with locals := before.locals} := by
  obtain ⟨before, setup, positive, callee, post, word, ready, called, actual, binding⟩ :=
    decoder_entry_data initial execution
  have cursor := setup_heap_state initial.arena.code setup
  exact ⟨before, setup, positive, callee, post, word, ready, cursor, called, actual, binding⟩

end InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_split
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_tail_heap
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_allocated_heap
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_heap_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.decoder_entry_heap

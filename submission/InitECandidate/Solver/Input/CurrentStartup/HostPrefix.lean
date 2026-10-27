import InitECandidate.Solver.Input.CurrentStartup.NormalHost
import InitECandidate.Solver.Input.CurrentStartup.DecoderReturn

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace NormalHost

theorem startup_returning (code) (installed : OriginalCode.Installed code)
    (routine : Code.Routine) (member : routine ∈ routines) :
    NormalHostEffects.Returning code (Code.body routine) := by
  simp only [routines, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sha256_init code installed
  · exact keccak_init code installed
  · exact ssz_init code installed
  · exact mpt_init code installed
  · exact u256_ws_init code installed
  · exact secp256k1_init code installed
  · exact bn254_init code installed
  · exact bls_precompiles_init code installed
  · exact ripemd160_init code installed
  · exact blake2_init code installed
  · exact header_init code installed
  · exact evm_init code installed
  · exact fork_init code installed

/-- The literal initializer sequence preserves host memory when it resumes.
No frame is asserted for its trapping or other nonresuming outcomes. -/
theorem startup_prefix (code) (installed : OriginalCode.Installed code)
    (functions : List Code.Routine) (inside : ∀ routine ∈ functions, routine ∈ routines) :
    NormalHostEffects.Preserves code (withTail functions .skip) := by
  induction functions with
  | nil => exact NormalHostEffects.skip code
  | cons routine rest ih =>
    apply NormalHostEffects.sequence code _ _
    · exact NormalHostEffects.call_body code (some none) (Code.name routine) []
        (Code.formals routine) (Code.body routine) (Code.shape routine)
        (Code.installed code installed routine)
        (startup_returning code installed routine (inside routine (by simp)))
    · exact ih (fun child member => inside child (by simp [member]))

end NormalHost

/-- Actual arena constants and host-input state at a genuine startup or
setup continuation. Heap cursor/alignment ownership is a separate obligation. -/
structure HostState (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  arena : ArenaState state
  little : state.be = false
  oracle : state.ffi.oracle = InitE.sourceOracle
  host : state.ffi.ffiState = Guest.guestHostMemory input

theorem startup_state (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source)
    (actual : evaluateHOLFiniteState source (withTail routines .skip) = (none, target)) : HostState input target := by
  have pure := NormalHost.startup_prefix source.code initial.arena.code routines (fun routine member => member)
  have host := pure source rfl (by rw [actual]; trivial)
  change (evaluateHOLFiniteState source (withTail routines .skip)).2.ffi.ffiState = source.ffi.ffiState at host
  rw [actual] at host
  have fields := evaluation_fields source target _ none actual
  exact ⟨prefix_state source target none initial.arena actual,
    fields.2.1.trans initial.little, (evaluation_oracle source target _ none actual).trans initial.oracle,
    host.trans initial.host⟩

namespace DecoderPrefix

theorem setup_host_preserves (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Preserves code (CallPrefix.program setupActions .skip) := by
  simp only [setupActions, actions_shape, List.take_succ_cons, List.take_zero, CallPrefix.program]
  refine NormalHostEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (NormalHost.alloc code installed) ?_
  refine NormalHostEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (NormalHost.alloc code installed) ?_
  refine NormalHostEffects.sequence code _ _
    (NormalHostEffects.call_body code (some none) (Code.name .memzero) _
      (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
      (Code.installed code installed .memzero) (NormalHost.memzero code installed)) ?_
  exact NormalHostEffects.declared code _ _ _ _
    (NormalHostEffects.declared code _ _ _ _ (NormalHostEffects.skip code))

theorem setup_arena_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (CallPrefix.program setupActions .skip) := by
  simp only [setupActions, actions_shape, List.take_succ_cons, List.take_zero, CallPrefix.program]
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc) ?_
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc) ?_
  refine GlobalEffects.sequence (key cursor) code _ _
    (Effects.call_preserves cursor code installed .memzero (some none) _) ?_
  exact GlobalEffects.declared (key cursor) code _ _ _ _
    (GlobalEffects.declared (key cursor) code _ _ _ _ (GlobalEffects.skip (key cursor) code))

/-- A genuine completed setup trace preserves its actual input host state
and declaration-derived metadata while retaining all four lexical bindings. -/
theorem setup_state {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (execution : CallPrefix.Execution source setupActions target) : HostState input target := by
  have same := execution.skip_erase
  have projected := congrArg Prod.fst (execution.project .skip)
  have normal : (evaluateHOLFiniteState source (CallPrefix.program setupActions .skip)).1 = none := by
    simpa only [CallPrefix.project, evaluateHOLFiniteState_skip] using projected
  have host := setup_host_preserves source.code initial.arena.code source rfl (by rw [normal]; trivial)
  have transferred := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.ffiState) same
  change (evaluateHOLFiniteState source (CallPrefix.program setupActions .skip)).2.ffi.ffiState = target.ffi.ffiState at transferred
  have arena : ArenaState target := by
    refine ⟨?_, ?_, execution.runtime.1.trans initial.arena.domain, ?_⟩
    · exact (execution.globals (key .scratch) (setup_arena_preserves .scratch source.code initial.arena.code)).trans initial.arena.scratch
    · exact (execution.globals (key .frame) (setup_arena_preserves .frame source.code initial.arena.code)).trans initial.arena.frame
    · rw [execution.runtime.2.2.2.1]; exact initial.arena.code
  exact ⟨arena, execution.runtime.2.1.trans initial.little,
    execution.runtime.2.2.2.2.trans initial.oracle, transferred.symm.trans (host.trans initial.host)⟩

/-- A real completed decoder prefix supplies its actual callee entry with
original host input, current arenas, byte order and source oracle. These
facts come from startup/setup execution, not a proposed decoder contract. -/
theorem decoder_entry_data {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (execution : CallPrefix.Execution source actions target) :
    ∃ before, CallPrefix.Execution source setupActions before ∧
      1 ≤ before.clock ∧ ∃ callee post, ∃ word : BitVec 64,
      HostState input (callEntryStateHOLFinite before callee) ∧
      lookupCodeHOLFinite before.code.lookup (Code.name .decode_host_input) [] =
        some (Code.body .decode_host_input, callee, .one) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite before callee) (Code.body .decode_host_input) =
        (some (.returned (.val (.word word))), post) ∧
      target = setVarHOLFinite (ofString "si") (.val (.word word)) {post with locals := before.locals} := by
  obtain ⟨before, setup, positive, callee, post, word, called, actual, binding⟩ :=
    reached_return initial.arena.code execution
  have ready := setup_state initial setup
  exact ⟨before, setup, positive, callee, post, word,
    ⟨⟨ready.arena.scratch, ready.arena.frame, ready.arena.domain, ready.arena.code⟩,
      ready.little, ready.oracle, ready.host⟩, called, actual, binding⟩

end DecoderPrefix

/-- Complete source observations have the original host input at the real
post-startup continuation, or stopped within startup. No validity, finite
list-size or future successful initializer premise is supplied. -/
theorem reached_host (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, middle) ∧
          HostState input middle ∧ evaluateHOLFiniteState middle afterStartup = (result, target)) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, split, classified, observation⟩ :=
    CurrentStartup.reached input outcome events terminates
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases split with continued | stopped
  · obtain ⟨middle, startupRun, arena, actual⟩ := continued
    have globals := Main.memory_globals origin
    have initial : HostState input (Main.memoryState origin) :=
      ⟨⟨globals.2.1, globals.2.2, entry.domain, entry.code⟩, entry.little, entry.oracle, entry.host⟩
    exact Or.inl ⟨middle, startupRun, startup_state input _ _ initial startupRun, actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.startup_returning
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.startup_prefix
#print axioms InitECandidate.Solver.Input.CurrentStartup.startup_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_host_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_arena_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.setup_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.reached_host

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.decoder_entry_data

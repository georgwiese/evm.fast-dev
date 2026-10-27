import InitECandidate.Solver.Input.CurrentStartup.Prefix
import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Input.CallPrefixGlobals
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The literal main prefix through its caught decoder call. These six
lexical actions retain out, z32, si and err_code at the real continuation. -/
def actions : List CallPrefix.Action := (CallPrefix.cutAt 6 afterStartup).1

def afterDecoder : ProgHOL 64 := (CallPrefix.cutAt 6 afterStartup).2

def decoderCall : ProgHOL 64 :=
  match (CallPrefix.cutAt 5 afterStartup).2 with
  | .seq called _ => called
  | _ => .skip

def handler : ProgHOL 64 :=
  match decoderCall with
  | .call (some (_, some (_, _, caught))) _ _ => caught
  | _ => .skip

theorem source_shape : afterStartup = CallPrefix.program actions afterDecoder :=
  (CallPrefix.reconstructAt 6 afterStartup).symm

theorem actions_shape : actions =
    [.scoped (ofString "out") .one (Code.name .alloc) [.const 256#64],
     .scoped (ofString "z32") .one (Code.name .alloc) [.const 32#64],
     .command (.call (some (none, none)) (Code.name .memzero)
       [.var .local (ofString "z32"), .const 32#64]),
     .declare (ofString "si") .one (.const 0#64),
     .declare (ofString "err_code") .one (.const 0#64),
     .command decoderCall] := by
  simp only [actions, handler, decoderCall, afterStartup, Main.afterMemory, Main.body,
    CallPrefix.cutAt, seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none, Code.name]

theorem decoder_shape : decoderCall = .call
    (some (some (.local, ofString "si"), some (ofString "SszErr", ofString "err_code", handler)))
    (Code.name .decode_host_input) [] := by
  simp only [actions, handler, decoderCall, afterStartup, Main.afterMemory, Main.body,
    CallPrefix.cutAt, seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none, Code.name]

/-- The real exception handler also preserves both cursors, including its
serialization, byte store, output call and terminal halt. -/
theorem handler_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code handler := by
  simp only [handler, decoderCall, afterStartup, Main.afterMemory, Main.body,
    CallPrefix.cutAt, seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .serialize_result) _ _
    (Code.formals .serialize_result) (Code.body .serialize_result) (Code.shape .serialize_result)
    (Code.installed code installed .serialize_result) (Effects.body_preserves cursor code installed .serialize_result) ?_
  refine GlobalEffects.sequence (key cursor) code _ _ (GlobalEffects.byte_store (key cursor) code _ _) ?_
  refine GlobalEffects.sequence (key cursor) code _ _
    (Effects.call_preserves cursor code installed .output_write (some none) _) ?_
  exact GlobalEffects.sequence (key cursor) code _ _
    (GlobalEffects.external (key cursor) code _ _ _ _ _) (GlobalEffects.returned (key cursor) code _)

theorem decoder_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code decoderCall := by
  rw [decoder_shape]
  exact GlobalEffects.caught_destination (key cursor) code (some (ofString "si"))
    (Code.name .decode_host_input) [] (Code.formals .decode_host_input) (Code.body .decode_host_input)
    (Code.shape .decode_host_input) (ofString "SszErr") (ofString "err_code") handler
    (Code.installed code installed .decode_host_input)
    (Effects.body_preserves cursor code installed .decode_host_input) (handler_preserves cursor code installed)

theorem prefix_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (CallPrefix.program actions .skip) := by
  rw [actions_shape]
  simp only [CallPrefix.program]
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc) ?_
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc) ?_
  refine GlobalEffects.sequence (key cursor) code _ _
    (Effects.call_preserves cursor code installed .memzero (some none) _) ?_
  refine GlobalEffects.declared (key cursor) code _ _ _ _ ?_
  refine GlobalEffects.declared (key cursor) code _ _ _ _ ?_
  exact GlobalEffects.sequence (key cursor) code _ _
    (decoder_preserves cursor code installed) (GlobalEffects.skip (key cursor) code)

/-- Reached lexical actions retain the declaration-derived domain, actual
code and both cursors, without restoring away the decoder's local bindings. -/
theorem reached_state {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : ArenaState source) (execution : CallPrefix.Execution source actions target) : ArenaState target := by
  refine ⟨?_, ?_, execution.runtime.1.trans initial.domain, ?_⟩
  · exact (execution.globals (key .scratch) (prefix_preserves .scratch source.code initial.code)).trans initial.scratch
  · exact (execution.globals (key .frame) (prefix_preserves .frame source.code initial.code)).trans initial.frame
  · rw [execution.runtime.2.2.2.1]
    exact initial.code

/-- All outcomes of the skip-sink prefix retain the real arena values. -/
theorem prefix_state (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source (CallPrefix.program actions .skip) = (result, target)) : ArenaState target := by
  have scratch := prefix_preserves .scratch source.code initial.code source rfl
  have frame := prefix_preserves .frame source.code initial.code source rfl
  rw [actual] at scratch frame
  have fields := evaluation_fields source target _ result actual
  refine ⟨(congrArg Prod.snd scratch).trans initial.scratch,
    (congrArg Prod.snd frame).trans initial.frame, fields.1.trans initial.domain, ?_⟩
  rw [fields.2.2.2]
  exact initial.code

/-- The two real alternatives at the decoder cut, retaining lexical
bindings on continuation and nonlocal observations on either alternative. -/
def Cut (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    (∃ current inner, CallPrefix.Execution source actions current ∧ ArenaState current ∧
      evaluateHOLFiniteState current afterDecoder = (result, inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
    (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program actions .skip) = (result, stopped) ∧
      ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧
      LocalEffects.erase post = LocalEffects.erase stopped)

/-- Exact nonlocal observation at the actual decoder cut. Lexical scope
restoration may change locals only; no decoder success or clock is assumed. -/
theorem split_execution (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source afterStartup = (result, post)) :
    Cut source result post := by
  rw [source_shape] at actual
  rcases CallPrefix.classify_frame source actions with stopped | reached
  · have same := stopped afterDecoder
    rw [actual] at same
    let output := evaluateHOLFiniteState source (CallPrefix.program actions .skip)
    have resultEq : result = output.1 := congrArg (fun observation => observation.1.1) same
    have clockEq : post.clock = output.2.clock := congrArg (fun observation => observation.1.2) same
    have frameEq : LocalEffects.erase post = LocalEffects.erase output.2 := congrArg Prod.snd same
    have computed : evaluateHOLFiniteState source (CallPrefix.program actions .skip) = (result, output.2) :=
      Prod.ext resultEq.symm rfl
    have invariant := prefix_state source output.2 result initial computed
    have postState : ArenaState post := by
      have globals := congrArg PanSemStateFiniteExact.globals frameEq
      have domain := congrArg PanSemStateFiniteExact.memaddrs frameEq
      have code := congrArg PanSemStateFiniteExact.code frameEq
      change post.code = output.2.code at code
      exact ⟨(congrArg (fun globals => globals.lookup (key .scratch)) globals).trans invariant.scratch,
        (congrArg (fun globals => globals.lookup (key .frame)) globals).trans invariant.frame,
        domain.trans invariant.domain, by rw [code]; exact invariant.code⟩
    exact Or.inr ⟨output.2, computed, invariant, postState, clockEq, frameEq⟩
  · obtain ⟨current, execution⟩ := reached
    have same := execution.observe afterDecoder
    rw [actual] at same
    have resultEq : result = (evaluateHOLFiniteState current afterDecoder).1 :=
      congrArg (fun observation => observation.1.1) same
    have clockEq : post.clock = (evaluateHOLFiniteState current afterDecoder).2.clock :=
      congrArg (fun observation => observation.1.2) same
    exact Or.inl ⟨current, (evaluateHOLFiniteState current afterDecoder).2, execution,
      reached_state initial execution, Prod.ext resultEq.symm rfl, clockEq, congrArg Prod.snd same⟩

/-- Join the decoder cut to a genuine complete source observation. The
arbitrary input and original terminal events are retained, with no future
success, positive clock or input-size assumption. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, middle) ∧
          ArenaState middle ∧ Cut middle result target) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, startup, classified, observation⟩ :=
    CurrentStartup.reached input outcome events terminates
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases startup with continued | stopped
  · obtain ⟨middle, startupRun, invariant, actual⟩ := continued
    exact Or.inl ⟨middle, startupRun, invariant, split_execution middle target result invariant actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.actions_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.decoder_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.handler_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.decoder_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.prefix_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.reached_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.prefix_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.split_execution

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.reached

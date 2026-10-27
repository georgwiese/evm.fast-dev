import InitECandidate.Solver.Input.CurrentHash.Effects
import InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix

namespace InitECandidate.Solver.Input.CurrentHash.HashPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open CurrentStartup (ArenaState)

abbrev decoderTail := CurrentStartup.DecoderPrefix.afterDecoder

def actions : List CallPrefix.Action := (CallPrefix.cutAt 2 decoderTail).1

def afterHash : ProgHOL 64 := (CallPrefix.cutAt 2 decoderTail).2

theorem source_shape : decoderTail = CallPrefix.program actions afterHash :=
  (CallPrefix.reconstructAt 2 decoderTail).symm

theorem actions_shape : actions =
    [.scoped (ofString "root") .one (Code.name .alloc) [.const 32#64],
     .command (.call (some (none, none)) (Code.name .htr_new_payload_request)
       [.var .local (ofString "si"), .var .local (ofString "root")])] := by
  simp only [actions, decoderTail, CurrentStartup.DecoderPrefix.afterDecoder,
    CurrentStartup.afterStartup, Main.afterMemory, Main.body, CallPrefix.cutAt,
    CurrentStartup.seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none, Code.name]

theorem prefix_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (CallPrefix.program actions .skip) := by
  rw [actions_shape]
  simp only [CallPrefix.program]
  refine GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc) ?_
  exact GlobalEffects.sequence (key cursor) code _ _
    (Effects.call_preserves cursor code installed .htr_new_payload_request (some none) _)
    (GlobalEffects.skip (key cursor) code)

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
      evaluateHOLFiniteState current afterHash = (result, inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
    (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program actions .skip) = (result, stopped) ∧
      ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧
      LocalEffects.erase post = LocalEffects.erase stopped)

/-- Exact nonlocal observation at the actual decoder cut. Lexical scope
restoration may change locals only; no decoder success or clock is assumed. -/
theorem split_execution (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source decoderTail = (result, post)) :
    Cut source result post := by
  rw [source_shape] at actual
  rcases CallPrefix.classify_frame source actions with stopped | reached
  · have same := stopped afterHash
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
    have same := execution.observe afterHash
    rw [actual] at same
    have resultEq : result = (evaluateHOLFiniteState current afterHash).1 :=
      congrArg (fun observation => observation.1.1) same
    have clockEq : post.clock = (evaluateHOLFiniteState current afterHash).2.clock :=
      congrArg (fun observation => observation.1.2) same
    exact Or.inl ⟨current, (evaluateHOLFiniteState current afterHash).2, execution,
      reached_state initial execution, Prod.ext resultEq.symm rfl, clockEq, congrArg Prod.snd same⟩

/-- Refine the existing genuine decoder cut, including its stopped alternative. -/
def ThroughDecoder (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    (∃ current inner, CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions current ∧
      ArenaState current ∧ Cut current result inner ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
    (∃ stopped, evaluateHOLFiniteState source
        (CallPrefix.program CurrentStartup.DecoderPrefix.actions .skip) = (result, stopped) ∧
      ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧
      LocalEffects.erase post = LocalEffects.erase stopped)

theorem refine_decoder {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (cut : CurrentStartup.DecoderPrefix.Cut source result post) :
    ThroughDecoder source result post := by
  rcases cut with reached | stopped
  · obtain ⟨current, inner, execution, arena, actual, clock, frame⟩ := reached
    exact Or.inl ⟨current, inner, execution, arena, split_execution current inner result arena actual, clock, frame⟩
  · exact Or.inr stopped

/-- Every terminating source execution reaches this hash cut or stops in one
of the actual earlier prefixes, retaining the original result and FFI events. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin)
          (CurrentStartup.withTail CurrentStartup.routines .skip) = (none, middle) ∧
          ArenaState middle ∧ ThroughDecoder middle result target) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin)
          (CurrentStartup.withTail CurrentStartup.routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, cut, classified, observation⟩ :=
    CurrentStartup.DecoderPrefix.reached input outcome events terminates
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases cut with continued | stopped
  · obtain ⟨middle, actual, arena, decoder⟩ := continued
    exact Or.inl ⟨middle, actual, arena, refine_decoder decoder⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentHash.HashPrefix

#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.actions_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.prefix_preserves
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.reached_state
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.prefix_state
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.split_execution
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.refine_decoder
#print axioms InitECandidate.Solver.Input.CurrentHash.HashPrefix.reached

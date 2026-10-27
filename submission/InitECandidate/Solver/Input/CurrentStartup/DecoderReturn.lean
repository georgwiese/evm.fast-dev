import InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual rejection handler always stops. Its final return stays
inside the real serialize-result scope; no output success is assumed. -/
theorem handler_stops : NoFallthrough handler := by
  simp only [handler, decoderCall, afterStartup, Main.afterMemory, Main.body,
    CallPrefix.cutAt, seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  apply NoFallthrough.scoped
  repeat' apply NoFallthrough.sequence
  exact NoFallthrough.returned _

/-- A real continuation past main's caught decoder call received a checked
word return from the actual decoder. It cannot be a fallthrough of the
rejection handler. The real caller binding and paid clock are derived. -/
theorem normal_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source decoderCall = (none, target)) :
    1 ≤ source.clock ∧ ∃ callee post, ∃ word : BitVec 64,
      lookupCodeHOLFinite source.code.lookup (Code.name .decode_host_input) [] =
        some (Code.body .decode_host_input, callee, .one) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (Code.body .decode_host_input) =
        (some (.returned (.val (.word word))), post) ∧
      target = setVarHOLFinite (ofString "si") (.val (.word word)) {post with locals := source.locals} := by
  have entry : source.code.lookup (Code.name .decode_host_input) = some ([], Code.body .decode_host_input, .one) :=
    by simpa only [Code.formals, Code.shape, Code.entry, Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
      Guest.Software.guestFn_decode_host_input, shapeToHOL, List.map_nil]
      using Code.installed source.code installed .decode_host_input
  obtain ⟨callee, called⟩ := Main.nullary_environment source.code.lookup (Code.name .decode_host_input)
    (Code.body .decode_host_input) entry
  rw [decoder_shape] at normal
  obtain ⟨positive, post, value, actual, checked, binding⟩ := CallNormal.assigned_caught_stops
    source target (ofString "si") (Code.name .decode_host_input) [] []
    (Code.body .decode_host_input) callee .one (ofString "SszErr") (ofString "err_code") handler
    rfl called (fun current _ => handler_stops current) normal
  have scalar := (shapeEqHOL_eq_true _ _).mp checked
  cases value with
  | val payload =>
    cases payload with
    | word word => exact ⟨positive, callee, post, word, called, actual, binding⟩
  | rStruct fields => simp only [shapeOfHOLExact] at scalar; cases scalar
  | nStruct name fields => simp only [shapeOfHOLExact] at scalar; cases scalar

def setupActions : List CallPrefix.Action := actions.take 5

theorem actions_setup : actions = setupActions ++ [.command decoderCall] := by
  simp only [setupActions, actions_shape]
  rfl

/-- Extract the real decoder invocation from the completed main prefix.
The setup execution retains the lexical output/zero-buffer bindings. -/
theorem reached_return {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (installed : OriginalCode.Installed source.code)
    (execution : CallPrefix.Execution source actions target) :
    ∃ before, CallPrefix.Execution source setupActions before ∧
      1 ≤ before.clock ∧ ∃ callee post, ∃ word : BitVec 64,
      lookupCodeHOLFinite before.code.lookup (Code.name .decode_host_input) [] =
        some (Code.body .decode_host_input, callee, .one) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite before callee) (Code.body .decode_host_input) =
        (some (.returned (.val (.word word))), post) ∧
      target = setVarHOLFinite (ofString "si") (.val (.word word)) {post with locals := before.locals} := by
  rw [actions_setup] at execution
  obtain ⟨before, setup, last⟩ := execution.split setupActions [.command decoderCall]
  have actual : evaluateHOLFiniteState before decoderCall = (none, target) := by
    cases last.singleton
    assumption
  have beforeCode : OriginalCode.Installed before.code := by
    rw [setup.runtime.2.2.2.1]
    exact installed
  obtain ⟨positive, callee, post, word, called, returned, binding⟩ := normal_return before target beforeCode actual
  exact ⟨before, setup, positive, callee, post, word, called, returned, binding⟩

end InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.handler_stops
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.normal_return

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.actions_setup
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderPrefix.reached_return

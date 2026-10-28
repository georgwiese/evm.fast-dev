import InitECandidate.Solver.Input.CurrentStartup.MptInitialized
import InitECandidate.Solver.Input.CurrentStartup.MainDecodedRoot
import InitECandidate.Solver.Input.CurrentStartup.StatelessReturned

namespace InitECandidate.Solver.Input.CurrentStartup.MainDecodedState
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original decoded witness snapshot at main's actual after-decoder
state, including its real si binding and exact selected decoder run. -/
theorem current {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701134824 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin : DecoderOrigin, ∃ record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
      MainSeparatedInput.RootRun input origin ∧ target.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
      WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input target origin.pointer origin.word
        record gasWord requestRecord payloadLength := by
  obtain ⟨origin, run, si, frame, clock⟩ := MainDecodedRoot.current initial heap offsets execution
  obtain ⟨record, gasWord, requestRecord, payloadLength, data⟩ := StatelessReturned.rooted origin input run gas
  exact ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, data.of_frame frame clock⟩

def Cut (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  (∃ current inner, ∃ origin : DecoderOrigin, ∃ record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
    CallPrefix.Execution source DecoderPrefix.actions current ∧ ArenaState current ∧
    MainSeparatedInput.RootRun input origin ∧
    current.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
    WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input current origin.pointer origin.word
      record gasWord requestRecord payloadLength ∧
    evaluateHOLFiniteState current DecoderPrefix.afterDecoder = (result, inner) ∧
    post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
  (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program DecoderPrefix.actions .skip) = (result, stopped) ∧
    ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧ LocalEffects.erase post = LocalEffects.erase stopped)

/-- Price/physical facts are attached only after an actual continuing parser
return. Every real earlier stopped prefix is retained as the other alternative. -/
theorem cut (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : HostState input source)
    (heap : NormalHeapEffects.AtLeast 2701134824 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (actual : evaluateHOLFiniteState source afterStartup = (result, post))
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Cut input source result post := by
  rcases DecoderPrefix.split_execution source post result initial.arena actual with continued | stopped
  · obtain ⟨target, inner, execution, arena, suffixRun, clock, frame⟩ := continued
    obtain ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, data⟩ := current initial heap offsets execution gas
    exact Or.inl ⟨target, inner, origin, record, gasWord, requestRecord, payloadLength,
      execution, arena, run, si, data, suffixRun, clock, frame⟩
  · exact Or.inr stopped

/-- Complete source observations now supply physical witness/input/gas facts
at main's actual continuation. This is not a uniform runtime bound. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
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
      ((MptWorkspace.main_cells input origin middle entry startupRun).2)
      (EarlyWorkspace.main_offsets input origin middle entry startupRun) actual gas⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentStartup.MainDecodedState

#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.current
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.cut
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.reached

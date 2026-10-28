import InitECandidate.Solver.Input.CurrentStartup.MptInitialized
import InitECandidate.Solver.Input.CurrentHash.RootEntry
import InitECandidate.Solver.Input.CurrentHash.AllocatorCost

namespace InitECandidate.Solver.Input.CurrentHash.RootCut
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open CurrentStartup (ArenaState)

theorem prefix_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (CallPrefix.program RootEntry.actions .skip) := by
  rw [RootEntry.actions_shape]
  simp only [CallPrefix.program]
  exact GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (Effects.body_preserves cursor code installed .alloc)
    (GlobalEffects.skip (key cursor) code)

/-- Includes every failed root allocation; no normal return/room assumption. -/
theorem prefix_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program RootEntry.actions .skip) 2 := by
  rw [RootEntry.actions_shape]
  exact WitnessRadix.PersistentAlloc.scoped_price code installed (ofString "root") .one [.const 32#64] .skip 0 (ClockCost.skip code)

theorem prefix_state (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source (CallPrefix.program RootEntry.actions .skip) = (result, target)) : ArenaState target := by
  have scratch := prefix_preserves .scratch source.code initial.code source rfl
  have frame := prefix_preserves .frame source.code initial.code source rfl
  rw [actual] at scratch frame
  have fields := evaluation_fields source target _ result actual
  refine ⟨(congrArg Prod.snd scratch).trans initial.scratch, (congrArg Prod.snd frame).trans initial.frame,
    fields.1.trans initial.domain, ?_⟩
  rw [fields.2.2.2]
  exact initial.code

/-- The real after-decoder execution either reaches the hash caller with its
physical input image, or stops in the actual root-allocation prefix. -/
def Cut (input : Guest.InputBlob) (decoded : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (extra : PanSemStateFiniteExact 64 Guest.HostMemory → Prop := fun _ => True) : Prop :=
  (∃ current inner, ∃ origin : CurrentStartup.DecoderOrigin,
    ∃ record gasWord requestRecord root array : BitVec 64, ∃ payloadLength start size : Nat,
      CallPrefix.Execution decoded RootEntry.actions current ∧
      RootEntry.Ready input decoded current origin record gasWord requestRecord root array payloadLength start size ∧
      extra current ∧ evaluateHOLFiniteState current RootEntry.afterRoot = (result, inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
  (∃ stopped, evaluateHOLFiniteState decoded (CallPrefix.program RootEntry.actions .skip) = (result, stopped) ∧
    ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧ LocalEffects.erase post = LocalEffects.erase stopped)

theorem cut {input : Guest.InputBlob} {source decoded post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (initial : CurrentStartup.HostState input source)
    (heap : NormalHeapEffects.AtLeast 2701134824 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (decoder : CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions decoded)
    (actual : evaluateHOLFiniteState decoded HashPrefix.decoderTail = (result, post))
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Cut input decoded result post := by
  have arena := CurrentStartup.DecoderPrefix.reached_state initial.arena decoder
  rw [RootEntry.source_shape] at actual
  rcases CallPrefix.classify_frame decoded RootEntry.actions with stopped | reached
  · have same := stopped RootEntry.afterRoot
    rw [actual] at same
    let output := evaluateHOLFiniteState decoded (CallPrefix.program RootEntry.actions .skip)
    have resultEq : result = output.1 := congrArg (fun observation => observation.1.1) same
    have clockEq : post.clock = output.2.clock := congrArg (fun observation => observation.1.2) same
    have frameEq : LocalEffects.erase post = LocalEffects.erase output.2 := congrArg Prod.snd same
    have computed : evaluateHOLFiniteState decoded (CallPrefix.program RootEntry.actions .skip) = (result, output.2) :=
      Prod.ext resultEq.symm rfl
    have invariant := prefix_state decoded output.2 result arena computed
    have postState : ArenaState post := by
      have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frameEq
      have domain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frameEq
      have code := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) frameEq
      change post.code = output.2.code at code
      exact ⟨(congrArg (fun table => table.lookup (key .scratch)) globals).trans invariant.scratch,
        (congrArg (fun table => table.lookup (key .frame)) globals).trans invariant.frame,
        domain.trans invariant.domain, by rw [code]; exact invariant.code⟩
    exact Or.inr ⟨output.2, computed, invariant, postState, clockEq, frameEq⟩
  · obtain ⟨current, execution⟩ := reached
    obtain ⟨origin, record, gasWord, requestRecord, root, array, payloadLength, start, size, data⟩ :=
      RootEntry.allocated initial heap offsets decoder execution gas
    have same := execution.observe RootEntry.afterRoot
    rw [actual] at same
    have resultEq : result = (evaluateHOLFiniteState current RootEntry.afterRoot).1 :=
      congrArg (fun observation => observation.1.1) same
    have clockEq : post.clock = (evaluateHOLFiniteState current RootEntry.afterRoot).2.clock :=
      congrArg (fun observation => observation.1.2) same
    exact Or.inl ⟨current, (evaluateHOLFiniteState current RootEntry.afterRoot).2, origin, record, gasWord, requestRecord,
      root, array, payloadLength, start, size, execution, data, True.intro, Prod.ext resultEq.symm rfl, clockEq, congrArg Prod.snd same⟩

def ThroughDecoder (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (extra : PanSemStateFiniteExact 64 Guest.HostMemory → Prop := fun _ => True) : Prop :=
  (∃ decoded inner, CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions decoded ∧
    Cut input decoded result inner extra ∧ post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner) ∨
  (∃ stopped, evaluateHOLFiniteState source (CallPrefix.program CurrentStartup.DecoderPrefix.actions .skip) = (result, stopped) ∧
    ArenaState stopped ∧ ArenaState post ∧ post.clock = stopped.clock ∧ LocalEffects.erase post = LocalEffects.erase stopped)

/-- Add a property derived from the same actual reached root prefix without
copying the source-observation split or discarding any stopped alternatives. -/
theorem Cut.with_ready {input : Guest.InputBlob} {decoded post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (data : Cut input decoded result post)
    (extra : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (holds : ∀ current, CallPrefix.Execution decoded RootEntry.actions current → extra current) :
    Cut input decoded result post extra := by
  rcases data with continued | stopped
  · obtain ⟨current, inner, origin, record, gasWord, requestRecord, root, array, payloadLength, start, size,
      execution, ready, trivial, actual, clock, frame⟩ := continued
    exact Or.inl ⟨current, inner, origin, record, gasWord, requestRecord, root, array, payloadLength, start, size,
      execution, ready, holds current execution, actual, clock, frame⟩
  · exact Or.inr stopped

theorem ThroughDecoder.with_ready {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (data : ThroughDecoder input source result post)
    (extra : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (holds : ∀ decoded current, CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions decoded →
      CallPrefix.Execution decoded RootEntry.actions current → extra current) :
    ThroughDecoder input source result post extra := by
  rcases data with continued | stopped
  · obtain ⟨decoded, inner, execution, actual, clock, frame⟩ := continued
    exact Or.inl ⟨decoded, inner, execution, actual.with_ready extra (fun current reached => holds decoded current execution reached), clock, frame⟩
  · exact Or.inr stopped

theorem refine_decoder {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (initial : CurrentStartup.HostState input source)
    (heap : NormalHeapEffects.AtLeast 2701134824 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (original : CurrentStartup.MainDecodedState.Cut input source result post) : ThroughDecoder input source result post := by
  rcases original with continued | stopped
  · obtain ⟨decoded, inner, origin, record, gasWord, requestRecord, payloadLength, execution, arena, run, si, snapshot,
      actual, clock, frame⟩ := continued
    exact Or.inl ⟨decoded, inner, execution, cut initial heap offsets execution actual gas, clock, frame⟩
  · exact Or.inr stopped

/-- Actual whole-source observations reach this genuine hash caller or one of
the earlier stopped paths, with their original outcome and FFI trace retained. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (none, middle) ∧
          CurrentStartup.HostState input middle ∧ ThroughDecoder input middle result target) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, startup, classified, observation⟩ :=
    CurrentStartup.MainDecodedState.reached input outcome events terminates gas
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases startup with continued | stopped
  · obtain ⟨middle, startupRun, initial, actual⟩ := continued
    exact Or.inl ⟨middle, startupRun, initial, refine_decoder initial
      ((CurrentStartup.MptWorkspace.main_cells input origin middle entry startupRun).2)
      (CurrentStartup.EarlyWorkspace.main_offsets input origin middle entry startupRun) gas actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentHash.RootCut

#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.prefix_preserves
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.prefix_state
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.cut
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.refine_decoder
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.reached

#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.Cut.with_ready
#print axioms InitECandidate.Solver.Input.CurrentHash.RootCut.ThroughDecoder.with_ready

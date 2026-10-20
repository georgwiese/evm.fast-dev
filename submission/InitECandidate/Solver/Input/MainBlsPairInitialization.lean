import InitECandidate.Solver.Input.MainBlsPairProgram

namespace InitECandidate.Solver.Input.Main.BlsPairInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) := InitializerAllocationAliases.step source cursor (block kind)

/-- Each original pair-buffer initializer calls the initialized constant
routine, allocates its real buffer and assigns both real aliases. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString (paramsName kind)) = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (room : cursor + 192 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (body kind) = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor kind with clock := source.clock - 2}) := by
  have guarded : evaluateHOLFiniteState source (WordTableInitialization.guard (paramsName kind)) = (none,source) := by
    simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have initialized := BlsConstants.initialized_call source constants installed binding nonzero (by omega)
  let ready := {source with clock := source.clock - 1}
  have allocated := InitializerAllocationAliases.step_execute ready cursor (block kind) (.return (.const 0#64)) installed scalars heap (valid kind) room aligned (by change 1 ≤ source.clock - 1; omega)
  have clock : source.clock - 1 - 1 = source.clock - 2 := by omega
  have current : evaluateHOLFiniteState ready (allocationTail kind) = evaluateHOLFiniteState {template source cursor kind with clock := source.clock - 2} (.return (.const 0#64)) := by
    simpa only [allocationTail,InitializerAllocationAliases.withTail,ready,InitializerAllocationAliases.step_clock,clock,template] using allocated
  rw [body_shape,StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _),
    StateSteps.next_sequence source ready constantsCall _ initialized (by change source.clock - 1 ≤ source.clock; omega),current]
  exact BuildEntry.zero_return {template source cursor kind with clock := source.clock - 2}

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor kind = {template source cursor kind with locals := locals} := by
  unfold template InitializerAllocationAliases.step
  rw [InitializerAllocations.template_locals source cursor [(block kind).allocation] locals]
  exact InitializerAliases.template_locals (InitializerAllocations.template source cursor [(block kind).allocation]) (BitVec.ofNat 64 cursor) (block kind).aliases locals

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (clock : Nat) :
    template {source with clock := clock} cursor kind = {template source cursor kind with clock := clock} := InitializerAllocationAliases.step_clock source cursor (block kind) clock

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) :
    (template source cursor kind).locals = source.locals := by
  unfold template InitializerAllocationAliases.step
  rw [InitializerAliases.template_locals_value,InitializerAllocations.template_locals_value]

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString (paramsName kind)) = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (room : cursor + 192 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString (function kind)) []) = (none,{template source cursor kind with clock := source.clock - 3}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString (function kind)) (body kind) (original_code kind source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor kind constants installed scalars heap zero binding nonzero room aligned (by change 2 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString (function kind)) [] [] (body kind) callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor kind with clock := entry.clock - 2}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => template state cursor kind) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor kind (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (template_locals source cursor kind callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor kind with locals := source.locals} = template source cursor kind := by rw [← template_locals_value source cursor kind]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 2 = 3 from rfl] using actual

end InitECandidate.Solver.Input.Main.BlsPairInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.call_execute

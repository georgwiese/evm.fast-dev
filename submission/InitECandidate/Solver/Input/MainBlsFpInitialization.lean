import InitECandidate.Solver.Input.MainBlsFpMemory
import InitECandidate.Solver.Input.InitializerBufferFields

namespace InitECandidate.Solver.Input.Main.BlsFpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocationAliases.step source cursor block
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) := memoryTemplate (allocated source cursor) (BitVec.ofNat 64 cursor) constants

theorem allocated_params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "fp_accel_params") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp only [allocated,InitializerAllocationAliases.step,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,block,InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem allocated_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "fp_accel_zero") = some (.val (.word (BitVec.ofNat 64 cursor + 96#64))) := by
  simp only [allocated,InitializerAllocationAliases.step,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,block,InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem allocated_constants (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "bls_c") = source.globals.lookup (ofString "bls_c") := by
  apply InitializerAllocationAliases.step_other source cursor block (ofString "bls_c") (by decide) (by decide)
  intro action member
  simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

private theorem memory_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer constants : BitVec 64) (clock : Nat) :
    memoryTemplate {source with clock := clock} pointer constants = {memoryTemplate source pointer constants with clock := clock} := rfl

private theorem memory_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer constants : BitVec 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    memoryTemplate {source with locals := locals} pointer constants = {memoryTemplate source pointer constants with locals := locals} := rfl

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) (clock : Nat) :
    template {source with clock := clock} cursor constants = {template source cursor constants with clock := clock} := by
  unfold template allocated
  rw [InitializerAllocationAliases.step_clock source cursor block clock]
  exact memory_clock (InitializerAllocationAliases.step source cursor block) (BitVec.ofNat 64 cursor) constants clock

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor constants = {template source cursor constants with locals := locals} := by
  unfold template allocated
  rw [InitializerAllocationAliases.step_locals source cursor block locals]
  exact memory_locals (InitializerAllocationAliases.step source cursor block) (BitVec.ofNat 64 cursor) constants locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) :
    (template source cursor constants).locals = source.locals := by
  simp only [template,memoryTemplate]
  exact InitializerAllocationAliases.step_locals_value source cursor block

/-- Entire original657 body, including its current constant guard, actual
allocation/aliases and both mapped memory calls. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (constantArena : AllocatedBytes.Arena constants 7136) (constantAligned : constants.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 240 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 10 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor constants with clock := source.clock - 10}) := by
  have guarded : evaluateHOLFiniteState source (WordTableInitialization.guard "fp_accel_params") = (none,source) := by
    simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have initialized := BlsConstants.initialized_call source constants installed binding nonzero (by omega)
  let first := {source with clock := source.clock - 1}
  have setup := InitializerAllocationAliases.step_execute first cursor block memoryTail installed scalars heap valid room aligned (by change 1 ≤ source.clock - 1; omega)
  have clock2 : source.clock - 1 - 1 = source.clock - 2 := by omega
  have allocationRun : evaluateHOLFiniteState first allocationTail = evaluateHOLFiniteState {allocated source cursor with clock := source.clock - 2} memoryTail := by
    simpa only [allocationTail,InitializerAllocationAliases.withTail,first,InitializerAllocationAliases.step_clock,clock2,allocated] using setup
  let ready := {allocated source cursor with clock := source.clock - 2}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (allocated source cursor) (source.clock - 2)).trans (InitializerAllocationAliases.step_context source cursor block)
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have currentBinding : ready.globals.lookup (ofString "bls_c") = some (.val (.word constants)) := (allocated_constants source cursor).trans binding
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have tailRun := memory_execute ready (BitVec.ofNat 64 cursor) constants currentInstalled (allocated_params source cursor) (allocated_zero source cursor) currentBinding currentDomain
    ⟨by rw [number]; exact lower,by rw [number]; exact room⟩ (by rw [number]; exact aligned) constantArena constantAligned (by change 8 ≤ source.clock - 2; omega)
  rw [body_shape,StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _),
    StateSteps.next_sequence source first BlsPairInitialization.constantsCall _ initialized (by change source.clock - 1 ≤ source.clock; omega),allocationRun]
  have clock10 : source.clock - 2 - 8 = source.clock - 10 := by omega
  simpa only [ready,memory_clock,clock10,template] using tailRun

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (constantArena : AllocatedBytes.Arena constants 7136) (constantAligned : constants.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 240 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 11 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "fp_accel_init") []) = (none,{template source cursor constants with clock := source.clock - 11}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "fp_accel_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor constants installed scalars heap zero binding nonzero domain constantArena constantAligned lower room aligned (by change 10 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "fp_accel_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor constants with clock := entry.clock - 10}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => template state cursor constants) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor constants (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (template_locals source cursor constants callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor constants with locals := source.locals} = template source cursor constants := by rw [← template_locals_value source cursor constants]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 10 = 11 from rfl] using actual

end InitECandidate.Solver.Input.Main.BlsFpInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.allocated_params
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.allocated_zero
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.allocated_constants
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.call_execute

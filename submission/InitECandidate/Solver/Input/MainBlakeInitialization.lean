import InitECandidate.Solver.Input.MainBlakeProgram
import InitECandidate.Solver.Input.InitializerBufferPlanFields

namespace InitECandidate.Solver.Input.Main.BlakeInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocationAliases.template source cursor blocks
def tables (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sigmaPointer ivPointer : BitVec 64) :=
  InitializerWords.written (InitializerWords.written source sigmaPointer 0 sigma) ivPointer 0 iv
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := tables (allocated source cursor) (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 (cursor + 80))

theorem allocated_sigma (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "b2_sigma") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp only [allocated,blocks,InitializerAllocationAliases.template,InitializerAllocationAliases.step,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,sigmaBlock,ivBlock,roundBlock,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem allocated_iv (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "b2_iv") = some (.val (.word (BitVec.ofNat 64 (cursor + 80)))) := by
  simp only [allocated,blocks,InitializerAllocationAliases.template,InitializerAllocationAliases.step,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,sigmaBlock,ivBlock,roundBlock,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sigmaPointer ivPointer : BitVec 64)
    (sigmaBinding : source.globals.lookup (ofString "b2_sigma") = some (.val (.word sigmaPointer)))
    (ivBinding : source.globals.lookup (ofString "b2_iv") = some (.val (.word ivPointer))) (domain : source.memaddrs = InitE.ordinaryDomain)
    (sigmaArena : AllocatedBytes.Arena sigmaPointer 80) (sigmaAligned : sigmaPointer.toNat % 8 = 0)
    (ivArena : AllocatedBytes.Arena ivPointer 64) (ivAligned : ivPointer.toNat % 8 = 0) :
    evaluateHOLFiniteState source sigmaStores = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (tables source sigmaPointer ivPointer)) := by
  have first := InitializerWords.execute source "b2_sigma" sigmaPointer 0 80 sigma ivStores sigmaBinding domain sigmaArena sigmaAligned (by decide) (by rw [sigma_length])
  let middle := InitializerWords.written source sigmaPointer 0 sigma
  have second := InitializerWords.execute middle "b2_iv" ivPointer 0 64 iv (.return (.const 0#64)) ivBinding domain ivArena ivAligned (by decide) (by rw [iv_length])
  rw [sigmaStores,first,ivStores,second]
  exact BuildEntry.zero_return (tables source sigmaPointer ivPointer)

private theorem tables_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sigmaPointer ivPointer : BitVec 64) (clock : Nat) :
    tables {source with clock := clock} sigmaPointer ivPointer = {tables source sigmaPointer ivPointer with clock := clock} := by
  simp only [tables,InitializerWords.written_clock]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template allocated
  rw [InitializerAllocationAliases.template_clock source cursor blocks clock]
  exact tables_clock (InitializerAllocationAliases.template source cursor blocks) (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 (cursor + 80)) clock

private theorem written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    InitializerWords.written {source with locals := locals} pointer offset words = {InitializerWords.written source pointer offset words with locals := locals} := rfl

private theorem tables_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sigmaPointer ivPointer : BitVec 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    tables {source with locals := locals} sigmaPointer ivPointer = {tables source sigmaPointer ivPointer with locals := locals} := by
  simp only [tables,written_locals]

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template allocated
  rw [InitializerAllocationAliases.template_locals source cursor blocks locals]
  exact tables_locals (InitializerAllocationAliases.template source cursor blocks) (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 (cursor + 80)) locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (template source cursor).locals = source.locals := by
  have same : {source with locals := source.locals} = source := rfl
  have preserved := congrArg (fun state => state.locals) (template_locals source cursor source.locals)
  rw [same] at preserved
  exact preserved

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  unfold template tables InitializerWords.written
  rw [InitializerAllocations.context_memory,InitializerAllocations.context_memory]
  exact InitializerAllocationAliases.template_context source cursor blocks

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocationAliases.template_scalars source cursor blocks scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 408)))) := by
  have actual := InitializerAllocationAliases.template_heap source cursor blocks valid heap
  rw [total_bytes] at actual
  exact actual

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "b2_sigma") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 408 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  have guardRun : evaluateHOLFiniteState source (WordTableInitialization.guard "b2_sigma") = (none,source) := by
    simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have allocation := InitializerAllocationAliases.execute_prefix source cursor blocks sigmaStores installed scalars heap valid (by rw [total_bytes]; exact room) aligned (by rw [block_count]; exact enough)
  rw [block_count] at allocation
  let ready := {allocated source cursor with clock := source.clock - 3}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (allocated source cursor) (source.clock - 3)).trans (InitializerAllocationAliases.template_context source cursor blocks)
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have globals : ready.globals = (allocated source cursor).globals := by simp only [ready]
  have sigmaBinding : ready.globals.lookup (ofString "b2_sigma") = some (.val (.word (BitVec.ofNat 64 cursor))) := by rw [globals]; exact allocated_sigma source cursor
  have ivBinding : ready.globals.lookup (ofString "b2_iv") = some (.val (.word (BitVec.ofNat 64 (cursor + 80)))) := by rw [globals]; exact allocated_iv source cursor
  have number (offset : Nat) (inside : offset ≤ 408) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have baseNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by simpa using number 0 (by decide)
  have stored := stores_execute ready (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 (cursor + 80)) sigmaBinding ivBinding currentDomain
    ⟨by rw [baseNumber]; exact lower,by rw [baseNumber]; omega⟩ (by rw [baseNumber]; exact aligned)
    ⟨by rw [number 80 (by decide)]; omega,by rw [number 80 (by decide)]; omega⟩ (by rw [number 80 (by decide)]; omega)
  rw [body_shape,StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _),afterGuard,allocation]
  simpa only [ready,tables_clock,template,allocated] using stored

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "b2_sigma") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 408 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "blake2_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "blake2_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "blake2_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 3}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => template state cursor) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (template_locals source cursor callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor with locals := source.locals} = template source cursor := by rw [← template_locals_value source cursor]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 3 = 4 from rfl] using actual

end InitECandidate.Solver.Input.Main.BlakeInitialization

#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.allocated_sigma
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.allocated_iv
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.stores_execute
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.call_execute

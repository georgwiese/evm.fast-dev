import InitECandidate.Solver.Input.MainRipemdProgram

namespace InitECandidate.Solver.Input.Main.RipemdInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerWords.written (allocated source cursor) (BitVec.ofNat 64 cursor) 0 words

theorem allocated_tab (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "rmd_tab") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp only [allocated,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,actions,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template allocated
  rw [InitializerAllocations.template_clock,InitializerWords.written_clock]

private theorem written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    InitializerWords.written {source with locals := locals} pointer offset words = {InitializerWords.written source pointer offset words with locals := locals} := rfl

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template allocated
  rw [InitializerAllocations.template_locals source cursor actions locals]
  exact written_locals (InitializerAllocations.template source cursor actions) (BitVec.ofNat 64 cursor) 0 words locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (template source cursor).locals = source.locals := by
  have same : {source with locals := source.locals} = source := rfl
  have preserved := congrArg (fun state => state.locals) (template_locals source cursor source.locals)
  rw [same] at preserved
  exact preserved

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  unfold template InitializerWords.written
  rw [InitializerAllocations.context_memory]
  exact InitializerAllocations.template_context source cursor actions

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocations.template_scalars source cursor actions scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 456)))) := by
  have actual := InitializerAllocations.template_heap source cursor actions heap valid
  rw [total_bytes] at actual
  exact actual

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "rmd_tab") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 456 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 4}) := by
  have guardRun : evaluateHOLFiniteState source (WordTableInitialization.guard "rmd_tab") = (none,source) := by
    simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have allocationRun := InitializerAllocations.execute_prefix source cursor actions stores installed scalars heap valid (by rw [total_bytes]; exact room) aligned (by rw [action_count]; exact enough)
  rw [action_count] at allocationRun
  let ready := {allocated source cursor with clock := source.clock - 4}
  have currentDomain := (InitializerAllocations.domain_of_context source (allocated source cursor) (InitializerAllocations.template_context source cursor actions)).trans domain
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have stored := InitializerWords.execute ready "rmd_tab" (BitVec.ofNat 64 cursor) 0 160 words (.return (.const 0#64)) (allocated_tab source cursor) currentDomain
    ⟨by rw [number]; exact lower,by rw [number]; omega⟩ (by rw [number]; exact aligned) (by decide) (by rw [words_length])
  rw [body_shape,StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _),afterGuard,allocationRun]
  change evaluateHOLFiniteState ready stores = _
  rw [stores,stored]
  have returned := BuildEntry.zero_return (InitializerWords.written ready (BitVec.ofNat 64 cursor) 0 words)
  simpa only [BuildEntry.returnZero,ready,InitializerWords.written_clock,template] using returned

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "rmd_tab") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 456 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 5 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ripemd160_init") []) = (none,{template source cursor with clock := source.clock - 5}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "ripemd160_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 4 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "ripemd160_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 4}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
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
  simpa only [Nat.sub_sub,show 1 + 4 = 5 from rfl] using actual

end InitECandidate.Solver.Input.Main.RipemdInitialization

#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.allocated_tab
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.call_execute

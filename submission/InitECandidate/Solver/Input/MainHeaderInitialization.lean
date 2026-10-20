import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.WordTableFields
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Input.Main.HeaderInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_header_init with | .function fn => progToHOL fn.body | _ => .skip
def action := InitializerAllocations.constant "hdr_zero8" 8
def zeroCall : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.var .global (ofString "hdr_zero8"),.const 8#64]
def afterAllocation : ProgHOL 64 := .seq zeroCall (.return (.const 0#64))
def afterGuard := InitializerAllocations.withTail [action] afterAllocation

theorem body_shape : body = .seq (WordTableInitialization.guard "hdr_zero8") afterGuard := by
  simp only [body,WordTableInitialization.guard,afterGuard,action,afterAllocation,zeroCall,InitializerAllocations.withTail,InitializerAllocations.call,
    InitializerAllocations.constant,Guest.guestFn_header_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbol_member : ofString "hdr_zero8" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem valid : InitializerAllocations.Valid action := InitializerAllocations.valid_constant _ _ symbol_member (by decide) (by decide)

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "header_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 220 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_header_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_header_init,shapeToHOL,List.map_cons,List.map_nil] using checked

def zeroTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) := {source with memory := Zero.finalMemory source.memory pointer 8}
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := zeroTemplate (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor)

private theorem zero_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (clock : Nat) :
    zeroTemplate {source with clock := clock} pointer = {zeroTemplate source pointer with clock := clock} := rfl

private theorem zero_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    zeroTemplate {source with locals := locals} pointer = {zeroTemplate source pointer with locals := locals} := rfl

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template
  rw [InitializerAllocations.template_clock source cursor [action] clock]
  exact zero_clock (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) clock

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template
  rw [InitializerAllocations.template_locals source cursor [action] locals]
  exact zero_locals (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (template source cursor).locals = source.locals := by
  simp only [template,zeroTemplate]
  exact InitializerAllocations.template_locals_value source cursor [action]

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  unfold template zeroTemplate
  rw [InitializerAllocations.context_memory,InitializerAllocations.template_context]

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocations.template_scalars source cursor [action] scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 8)))) := by
  have actual := InitializerAllocations.template_heap source cursor [action] heap (by intro current member; have same := List.mem_singleton.mp member; subst current; exact valid)
  simpa only [template,zeroTemplate,InitializerAllocations.totalBytes,action,InitializerAllocations.constant,Nat.add_zero] using actual

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 8 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  have guarded : evaluateHOLFiniteState source (WordTableInitialization.guard "hdr_zero8") = (none,source) := by
    simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have allocated := InitializerAllocations.execute_prefix source cursor [action] afterAllocation installed scalars heap
    (by intro current member; have same := List.mem_singleton.mp member; subst current; exact valid)
    (by change cursor + (8 + 0) ≤ 33806089496; omega) aligned (by change 1 ≤ source.clock; omega)
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at allocated
  let ready := {InitializerAllocations.template source cursor [action] with clock := source.clock - 1}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (InitializerAllocations.template source cursor [action]) (source.clock - 1)).trans (InitializerAllocations.template_context source cursor [action])
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have binding : ready.globals.lookup (ofString "hdr_zero8") = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.allocated_binding source cursor action
  have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query)) [.var .global (ofString "hdr_zero8"),.const 8#64] = some (Zero.values (BitVec.ofNat 64 cursor) 8) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding,Zero.values]
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 8 := ⟨by rw [number]; exact lower,by rw [number]; exact room⟩
  have pointerAligned : (BitVec.ofNat 64 cursor).toNat % 8 = 0 := by rw [number]; exact aligned
  have cleared := Zero.call_execute ready _ (BitVec.ofNat 64 cursor) 8 args (Zero.original_code ready.code currentInstalled) (by decide) (by decide) pointerAligned
    (by intro offset inside multiple; exact AllocatedBytes.word_mapped ready (BitVec.ofNat 64 cursor) 8 offset currentDomain arena (by omega) pointerAligned multiple)
    (by change 2 ≤ source.clock - 1; omega)
  have clock : source.clock - 1 - 2 = source.clock - 3 := by omega
  have zeroRun : evaluateHOLFiniteState ready zeroCall = (none,{template source cursor with clock := source.clock - 3}) := by
    simpa only [zeroCall,Zero.price,show 8 / 32 + 8 % 32 / 8 + 1 = 2 from rfl,ready,zeroTemplate,template,clock] using cleared
  rw [body_shape,StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _),afterGuard,allocated]
  change evaluateHOLFiniteState ready afterAllocation = _
  rw [afterAllocation,StateSteps.next_sequence ready {template source cursor with clock := source.clock - 3} zeroCall _ zeroRun (by change source.clock - 3 ≤ source.clock - 1; omega)]
  exact BuildEntry.zero_return {template source cursor with clock := source.clock - 3}

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 8 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "header_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "header_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "header_init") [] [] body callee .one (.val (.word 0#64))
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

end InitECandidate.Solver.Input.Main.HeaderInitialization

#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.original_code
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.HeaderInitialization.call_execute

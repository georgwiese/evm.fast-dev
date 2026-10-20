import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.Input.InitializerWords
import InitECandidate.Solver.Input.InitializerFields

namespace InitECandidate.Solver.Input.WordTableInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def guard (name : String) : ProgHOL 64 := .ite (.cmp .notEqual (.var .global (ofString name)) (.const 0#64)) (.return (.const 0#64)) .skip
def stores (name : String) (words : List (BitVec 64)) : ProgHOL 64 := InitializerWords.stores name 0 words (.return (.const 0#64))
def body (action : InitializerAllocations.Action) (words : List (BitVec 64)) : ProgHOL 64 :=
  .seq (guard action.name) (InitializerAllocations.withTail [action] (stores action.name words))
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :=
  InitializerWords.written (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) 0 words

private theorem singleton_valid (action : InitializerAllocations.Action) (valid : InitializerAllocations.Valid action) :
    ∀ current,current ∈ [action] → InitializerAllocations.Valid current := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  exact valid

theorem allocated_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) :
    (InitializerAllocations.template source cursor [action]).globals.lookup (ofString action.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  rw [InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,HolFiniteMapExact.update,FUPDATE]

/-- A literal guarded table initializer executes its actual allocation and
all word stores. The bounds describe only current allocation room and code. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64))
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString action.name) = some (.val (.word 0#64))) (valid : InitializerAllocations.Valid action)
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + action.bytes ≤ 33806089496)
    (aligned : cursor % 8 = 0) (inside : 8 * words.length ≤ action.bytes) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (body action words) =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor action words with clock := source.clock - 1}) := by
  have guardRun : evaluateHOLFiniteState source (guard action.name) = (none,source) := by
    simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have allocation := InitializerAllocations.execute_prefix source cursor [action] (stores action.name words) installed scalars heap
    (singleton_valid action valid) (by simpa only [InitializerAllocations.totalBytes,Nat.add_zero] using room) aligned enough
  let ready := {InitializerAllocations.template source cursor [action] with clock := source.clock - 1}
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have currentDomain := (InitializerAllocations.domain_of_context source (InitializerAllocations.template source cursor [action])
    (InitializerAllocations.template_context source cursor [action])).trans domain
  have written := InitializerWords.execute ready action.name (BitVec.ofNat 64 cursor) 0 action.bytes words (.return (.const 0#64))
    (allocated_binding source cursor action) currentDomain ⟨by rw [number]; exact lower,by rw [number]; exact room⟩ (by rw [number]; exact aligned) (by decide) (by simpa only [Nat.zero_add] using inside)
  rw [body,StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _),allocation]
  simp only [List.length_cons,List.length_nil,Nat.zero_add]
  change evaluateHOLFiniteState ready (stores action.name words) = _
  rw [stores,written]
  have returned := BuildEntry.zero_return (InitializerWords.written ready (BitVec.ofNat 64 cursor) 0 words)
  simpa only [BuildEntry.returnZero,ready,InitializerWords.written_clock,template] using returned

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (clock : Nat) :
    template {source with clock := clock} cursor action words = {template source cursor action words with clock := clock} := by
  unfold template
  rw [InitializerAllocations.template_clock,InitializerWords.written_clock]

/-- Repeated real calls take the actual nonzero guard and leave memory,
globals and events intact. -/
theorem initialized_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (pointer : BitVec 64)
    (binding : source.globals.lookup (ofString action.name) = some (.val (.word pointer))) (nonzero : pointer ≠ 0#64) :
    evaluateHOLFiniteState source (body action words) = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) := by
  have guardRun : evaluateHOLFiniteState source (guard action.name) = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) := by
    have returned := BuildEntry.zero_return source
    simp only [BuildEntry.returnZero] at returned
    simp [guard,evaluateHOLFiniteState_ite,evalHOLExact,toExact,binding,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero,returned]
  rw [body,evaluateHOLFiniteState_seq_line780,guardRun]

private theorem written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    InitializerWords.written {source with locals := locals} pointer offset words = {InitializerWords.written source pointer offset words with locals := locals} := rfl

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor action words = {template source cursor action words with locals := locals} := by
  unfold template
  rw [InitializerAllocations.template_locals source cursor [action] locals]
  exact written_locals (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) 0 words locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :
    (template source cursor action words).locals = source.locals := by
  unfold template
  change (InitializerAllocations.template source cursor [action]).locals = source.locals
  exact InitializerAllocations.template_locals_value source cursor [action]

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

/-- Genuine nullary caller for the checked literal body, with both allocation
and caller ticks charged. Code lookup remains an actual fixed-program fact. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (function : MlS)
    (code : source.code.lookup function = some ([],body action words,.one))
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString action.name) = some (.val (.word 0#64))) (valid : InitializerAllocations.Valid action)
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + action.bytes ≤ 33806089496)
    (aligned : cursor % 8 = 0) (inside : 8 * words.length ≤ action.bytes) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) function []) = (none,{template source cursor action words with clock := source.clock - 2}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup function (body action words) code
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor action words installed scalars heap zero valid domain lower room aligned inside (by change 1 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none function [] [] (body action words) callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor action words with clock := entry.clock - 1}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => template state cursor action words) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor action words (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (template_locals source cursor action words callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor action words with locals := source.locals} = template source cursor action words := by
    rw [← template_locals_value source cursor action words]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 1 = 2 from rfl] using actual

theorem initialized_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (function : MlS) (pointer : BitVec 64)
    (code : source.code.lookup function = some ([],body action words,.one))
    (binding : source.globals.lookup (ofString action.name) = some (.val (.word pointer))) (nonzero : pointer ≠ 0#64) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) function []) = (none,{source with clock := source.clock - 1}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup function (body action words) code
  let entry := callEntryStateHOLFinite source callee
  have run := initialized_execute entry action words pointer binding nonzero
  exact evaluateHOLFiniteState_call_return_caller_locals source none function [] [] (body action words) callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite entry) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

end InitECandidate.Solver.Input.WordTableInitialization

#print axioms InitECandidate.Solver.Input.WordTableInitialization.allocated_binding
#print axioms InitECandidate.Solver.Input.WordTableInitialization.execute
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_clock
#print axioms InitECandidate.Solver.Input.WordTableInitialization.initialized_execute

#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_locals
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.WordTableInitialization.call_execute
#print axioms InitECandidate.Solver.Input.WordTableInitialization.initialized_call

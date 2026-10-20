import InitECandidate.Solver.Input.MainSszProgram
import InitECandidate.Solver.Input.MainEntry

namespace InitECandidate.Solver.Input.Main.SszInitialization
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerWords.written (allocated source cursor) (BitVec.ofNat 64 (cursor + 96)) 0 words

theorem allocated_hashes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (allocated source cursor).globals.lookup (ofString "zero_hashes") = some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) := by
  simp [allocated,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,actions,putGlobal,HolFiniteMapExact.update,FUPDATE]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template allocated
  rw [InitializerAllocations.template_clock,InitializerWords.written_clock]

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor).globals :=
  InitializerAllocations.template_scalars source cursor actions scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 2144)))) := by
  exact InitializerAllocations.template_heap source cursor actions heap valid

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notLength : key ≠ ofString "ssz_len_chunk")
    (notOffsets : key ≠ ofString "ssz_offs") (notHashes : key ≠ ofString "zero_hashes") :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocations.template_other source cursor actions key notHeap
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact notLength
  · exact notOffsets
  · exact notHashes

theorem table_arena (cursor : Nat) (lower : 2701131776 ≤ cursor) (room : cursor + 2144 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 96)) 2048 ∧ (BitVec.ofNat 64 (cursor + 96)).toNat % 8 = 0 := by
  have number : (BitVec.ofNat 64 (cursor + 96)).toNat = cursor + 96 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact ⟨⟨by rw [number]; omega,by rw [number]; omega⟩,by rw [number]; omega⟩

/-- First-time original SSZ initialization allocates its three buffers and
writes all256 actual literal words, preserving the real source memory elsewhere. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 2144 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  have guardRun : evaluateHOLFiniteState source guard = (none,source) := by
    simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [body_shape,StateSteps.next_sequence source source guard afterGuard guardRun (Nat.le_refl _),afterGuard]
  have allocationRun := InitializerAllocations.execute_prefix source cursor actions tableStores installed scalars heap valid room aligned enough
  rw [allocationRun]
  let ready := {allocated source cursor with clock := source.clock - 3}
  obtain ⟨arena,pointerAligned⟩ := table_arena cursor lower room aligned
  have storesRun := InitializerWords.execute ready "zero_hashes" (BitVec.ofNat 64 (cursor + 96)) 0 2048 words (.return (.const 0#64))
    (allocated_hashes source cursor) domain arena pointerAligned (by decide) (by rw [words_length])
  change evaluateHOLFiniteState ready tableStores = _
  rw [tableStores,storesRun]
  have returned := BuildEntry.zero_return (InitializerWords.written ready (BitVec.ofNat 64 (cursor + 96)) 0 words)
  simpa only [BuildEntry.returnZero,ready,InitializerWords.written_clock,template] using returned

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 2144 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "ssz_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "ssz_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 3}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have globalsClock := template_clock source cursor (source.clock - 1)
  have localFrame : template entry cursor = {template source cursor with clock := source.clock - 1,locals := callee} := by
    rfl
  rw [localFrame] at actual
  change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_init") []) = (none,{template source cursor with clock := source.clock - 1 - 3}) at actual
  simpa only [Nat.sub_sub,show 1 + 3 = 4 from rfl] using actual

end InitECandidate.Solver.Input.Main.SszInitialization

#print axioms InitECandidate.Solver.Input.Main.SszInitialization.allocated_hashes
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.table_arena
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.call_execute

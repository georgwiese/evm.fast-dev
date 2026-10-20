import InitECandidate.Solver.Input.MainEvmProgram
import InitECandidate.Solver.Input.InitializerZeroBuffer

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def nullTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerZeroBuffer.template source cursor nullAction
def emptyTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerZeroBuffer.template (nullTemplate source cursor) (cursor + 24) emptyAction
def finalTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template (emptyTemplate source cursor) (cursor + 32) [keyAction,headerAction]

theorem final_template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    finalTemplate {source with clock := clock} cursor = {finalTemplate source cursor with clock := clock} := by
  unfold finalTemplate emptyTemplate nullTemplate
  rw [(InitializerZeroBuffer.template_clock source cursor nullAction clock).2]
  rw [(InitializerZeroBuffer.template_clock (InitializerZeroBuffer.template source cursor nullAction) (cursor + 24) emptyAction clock).2]
  exact InitializerAllocations.template_clock _ _ _ _

theorem final_template_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    KeccakAbsorb.hashControl (finalTemplate source cursor) = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [nullAction,emptyAction,keyAction,headerAction]) := by
  have first := InitializerZeroBuffer.template_control source cursor nullAction
  have second := (InitializerZeroBuffer.template_control (nullTemplate source cursor) (cursor + 24) emptyAction).trans
    (InitializerAllocations.template_hash_control (InitializerAllocations.template source cursor [nullAction]) (nullTemplate source cursor) (cursor + 24) [emptyAction] first)
  exact InitializerAllocations.template_hash_control (InitializerAllocations.template (InitializerAllocations.template source cursor [nullAction]) (cursor + 24) [emptyAction]) (emptyTemplate source cursor) (cursor + 32) [keyAction,headerAction] second

theorem final_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 160 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 10 ≤ source.clock) :
    evaluateHOLFiniteState source afterSystem =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {finalTemplate source cursor with clock := source.clock - 10}) := by
  have nullRun := InitializerZeroBuffer.execute_prefix source cursor nullAction afterNullZero installed scalars heap actions_valid.2.2.1 domain lower
    (by change cursor + 24 ≤ _; omega) aligned (by change 5 ≤ source.clock; omega)
  let nullReady := {nullTemplate source cursor with clock := source.clock - 5}
  have nullContext : InitializerAllocations.context nullReady = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (InitializerZeroBuffer.template_context source cursor nullAction)
  have nullInstalled := InitializerAllocations.installed_of_context source nullReady nullContext installed
  have nullDomain := (InitializerAllocations.domain_of_context source nullReady nullContext).trans domain
  have nullScalars : OriginalScalarGlobals.Scalars nullReady.globals := InitializerAllocations.template_scalars source cursor [nullAction] scalars
  have nullHeap : nullReady.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 24)))) := by
    exact InitializerAllocations.template_heap source cursor [nullAction] heap (by intro action member; have same := List.mem_singleton.mp member; subst action; exact actions_valid.2.2.1)
  have emptyRun := InitializerZeroBuffer.execute_prefix nullReady (cursor + 24) emptyAction finalAllocations nullInstalled nullScalars nullHeap actions_valid.2.2.2.1 nullDomain
    (by omega) (by change cursor + 24 + 8 ≤ _; omega) (by omega) (by change 3 ≤ source.clock - 5; omega)
  let emptyReady := {emptyTemplate source cursor with clock := source.clock - 8}
  have emptyClock : source.clock - 5 - InitializerZeroBuffer.cost emptyAction = source.clock - 8 := by change source.clock - 5 - 3 = _; omega
  have emptyNormalized : evaluateHOLFiniteState nullReady afterNullZero = evaluateHOLFiniteState emptyReady finalAllocations := by
    change evaluateHOLFiniteState nullReady (InitializerZeroBuffer.program emptyAction finalAllocations) = _
    rw [emptyRun]
    congr 1
  have emptyContext : InitializerAllocations.context emptyReady = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans ((InitializerZeroBuffer.template_context (nullTemplate source cursor) (cursor + 24) emptyAction).trans (InitializerZeroBuffer.template_context source cursor nullAction))
  have emptyInstalled := InitializerAllocations.installed_of_context source emptyReady emptyContext installed
  have emptyDomain := (InitializerAllocations.domain_of_context source emptyReady emptyContext).trans domain
  have emptyScalars : OriginalScalarGlobals.Scalars emptyReady.globals :=
    InitializerAllocations.template_scalars (nullTemplate source cursor) (cursor + 24) [emptyAction] nullScalars
  have emptyHeap : emptyReady.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) := by
    have actual := InitializerAllocations.template_heap (nullTemplate source cursor) (cursor + 24) [emptyAction] nullHeap
      (by intro action member; have same := List.mem_singleton.mp member; subst action; exact actions_valid.2.2.2.1)
    change (InitializerAllocations.template (nullTemplate source cursor) (cursor + 24) [emptyAction]).globals.lookup (ofString "heap_ptr") = _
    simpa only [InitializerAllocations.totalBytes,emptyAction,InitializerAllocations.constant,Nat.add_zero,show cursor + 24 + 8 = cursor + 32 by omega] using actual
  have lastRun := InitializerAllocations.execute_prefix emptyReady (cursor + 32) [keyAction,headerAction] (.return (.const 0#64)) emptyInstalled emptyScalars emptyHeap
    (by intro action member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl; exact actions_valid.2.2.2.2.1; exact actions_valid.2.2.2.2.2)
    (by change cursor + 32 + (32 + (96 + 0)) ≤ _; omega) (by omega) (by change 2 ≤ source.clock - 8; omega)
  have lastClock : source.clock - 8 - [keyAction,headerAction].length = source.clock - 10 := by change source.clock - 8 - 2 = _; omega
  have finalRun : evaluateHOLFiniteState emptyReady finalAllocations = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {finalTemplate source cursor with clock := source.clock - 10}) := by
    rw [finalAllocations,lastRun]
    simpa only [emptyReady,InitializerAllocations.template_clock,lastClock,finalTemplate,BuildEntry.returnZero] using BuildEntry.zero_return {finalTemplate source cursor with clock := source.clock - 10}
  have nullNormalized : evaluateHOLFiniteState source afterSystem = evaluateHOLFiniteState nullReady afterNullZero := by
    exact nullRun
  rw [nullNormalized,emptyNormalized,finalRun]

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.final_template_clock
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.final_template_control
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.final_execute

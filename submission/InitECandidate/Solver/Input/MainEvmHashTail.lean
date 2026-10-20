import InitECandidate.Solver.Input.MainEvmAddress

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem after_hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 184 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 31 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source afterHash = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock = source.clock - 31 ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [systemAction,nullAction,emptyAction,keyAction,headerAction]) := by
  have allocated := InitializerAllocations.execute_prefix source cursor [systemAction] afterSystemAllocation installed scalars heap
    (by intro action member; have same := List.mem_singleton.mp member; subst action; exact actions_valid.2.1)
    (by change cursor + (24 + 0) ≤ _; omega) aligned (by change 1 ≤ source.clock; omega)
  let ready := {InitializerAllocations.template source cursor [systemAction] with clock := source.clock - 1}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (InitializerAllocations.template_context source cursor [systemAction])
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have currentScalars : OriginalScalarGlobals.Scalars ready.globals := InitializerAllocations.template_scalars source cursor [systemAction] scalars
  have currentHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 24)))) :=
    InitializerAllocations.template_heap source cursor [systemAction] heap (by intro action member; have same := List.mem_singleton.mp member; subst action; exact actions_valid.2.1)
  have binding : ready.globals.lookup (ofString "vm_system_address") = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.allocated_binding source cursor systemAction
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 24 := ⟨by rw [number]; exact lower,by rw [number]; omega⟩
  obtain ⟨post,run,clock,control⟩ := address_execute ready (cursor + 24) (BitVec.ofNat 64 cursor) currentInstalled currentScalars currentHeap binding currentDomain arena
    (by omega) (by omega) (by omega) (by change 30 ≤ source.clock - 1; omega)
  have actual : evaluateHOLFiniteState source afterHash = (some (.returned (.val (.word 0#64))),post) := by
    rw [afterHash,allocated]
    exact run
  refine ⟨post,actual,?_,?_⟩
  · change post.clock = source.clock - 1 - 30 at clock
    omega
  · have model : KeccakAbsorb.hashControl (InitializerAllocations.template ready (cursor + 24) [nullAction,emptyAction,keyAction,headerAction]) =
        KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [systemAction,nullAction,emptyAction,keyAction,headerAction]) := by
      unfold ready
      rw [InitializerAllocations.template_clock]
      rfl
    exact control.trans model

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.after_hash_execute

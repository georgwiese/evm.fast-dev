import InitECandidate.Solver.Input.MainEvmLoop
import InitECandidate.Solver.Input.MainEvmFinal
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxHeartbeats 200000

private theorem scope_control (source saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (clock : Nat) :
    KeccakAbsorb.hashControl (restore saved name (emptyLocalsHOLFinite {source with clock := clock})) = KeccakAbsorb.hashControl source := rfl

/-- The real scoped twenty-byte loop, final byte override and remaining
allocations/zero calls. No future loop or memory-call success is assumed. -/
theorem address_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (binding : source.globals.lookup (ofString "vm_system_address") = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 24)
    (lower : 2701131776 ≤ cursor) (room : cursor + 160 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 30 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source afterSystemAllocation = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock = source.clock - 30 ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [nullAction,emptyAction,keyAction,headerAction]) := by
  let entry := QueryBranch.bind source "i" 0#64
  have indexBinding : entry.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := by
    simp [entry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨loopPost,loopRun,loopClock,loopControl,loopGlobals,loopContext⟩ :
      ∃ post,evaluateHOLFiniteState entry systemLoop = (none,post) ∧ post.clock = source.clock - 20 ∧
        KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source ∧ post.globals = source.globals ∧
        InitializerAllocations.context post = InitializerAllocations.context source :=
    ⟨systemWalk entry pointer 0 20,
      system_loop_execute entry pointer 0 20 rfl binding indexBinding domain arena (by change 20 ≤ source.clock; omega),
      system_walk_clock entry pointer 0 20,system_walk_control entry pointer 0 20,
      system_walk_globals entry pointer 0 20,system_walk_context entry pointer 0 20⟩
  have loopInstalled := InitializerAllocations.installed_of_context source loopPost loopContext installed
  have loopDomain := (InitializerAllocations.domain_of_context source loopPost loopContext).trans domain
  have loopBinding : loopPost.globals.lookup (ofString "vm_system_address") = some (.val (.word pointer)) := by rw [loopGlobals]; exact binding
  have address : QueryBranch.eval loopPost (.op .add [.var .global (ofString "vm_system_address"),.const 19#64]) = some (.val (.word (byteAddress pointer 19))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,loopBinding,valueIsWord,valueWord,wordOpHOL,wordOp,byteAddress]
  have lastByte := ByteStore.execute loopPost _ (.const 254#64) (byteAddress pointer 19) 254#8 address rfl
    (AllocatedBytes.byte_mapped loopPost pointer 24 19 loopDomain arena (by decide))
  let bytePost := {loopPost with memory := ByteStore.put loopPost.memory loopPost.be (byteAddress pointer 19) 254#8}
  have currentHeap : bytePost.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) :=
    (congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup (ofString "heap_ptr")) loopGlobals).trans heap
  have currentScalars : OriginalScalarGlobals.Scalars bytePost.globals := loopGlobals.symm ▸ scalars
  have tailRun := final_execute bytePost cursor loopInstalled currentScalars currentHeap loopDomain lower room aligned (by change 10 ≤ loopPost.clock; omega)
  let target := emptyLocalsHOLFinite {finalTemplate bytePost cursor with clock := bytePost.clock - 10}
  have inner : evaluateHOLFiniteState entry (.seq systemLoop afterSystemLoop) = (some (.returned (.val (.word 0#64))),target) := by
    rw [StateSteps.next_sequence entry loopPost systemLoop _ loopRun (by change loopPost.clock ≤ source.clock; omega),afterSystemLoop]
    rw [StateSteps.next_sequence loopPost bytePost systemFinalByte _ lastByte (Nat.le_refl _)]
    exact tailRun
  have actual := ScalarScope.declare_execute source target "i" (.const 0#64) 0#64 (.seq systemLoop afterSystemLoop) (some (.returned (.val (.word 0#64)))) rfl inner
  refine ⟨restore source "i" target,actual,?_,?_⟩
  · change loopPost.clock - 10 = source.clock - 30
    omega
  · have mapped := InitializerAllocations.template_hash_control source bytePost cursor [nullAction,emptyAction,keyAction,headerAction] loopControl
    calc
      KeccakAbsorb.hashControl (restore source "i" target) = KeccakAbsorb.hashControl (finalTemplate bytePost cursor) := scope_control (finalTemplate bytePost cursor) source "i" (bytePost.clock - 10)
      _ = KeccakAbsorb.hashControl (InitializerAllocations.template bytePost cursor [nullAction,emptyAction,keyAction,headerAction]) := final_template_control bytePost cursor
      _ = _ := mapped

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.address_execute

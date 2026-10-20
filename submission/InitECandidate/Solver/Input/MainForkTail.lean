import InitECandidate.Solver.Input.MainForkAddresses
import InitECandidate.Solver.Input.MainForkLoop
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

private theorem scope_control (source saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    KeccakAbsorb.hashControl (restore saved name source) = KeccakAbsorb.hashControl source := rfl

theorem loop_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (binding : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 360)
    (lower : 2701131776 ≤ cursor) (room : cursor + 200 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 93 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source afterPrecompile = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 93 ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor (finalActions addresses)) := by
  let entry := QueryBranch.bind source "i" 0#64
  have indexBinding : entry.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := by
    simp [entry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨loopPost,loopRun,loopClock,loopControl,loopGlobals,loopContext⟩ :
      ∃ post,evaluateHOLFiniteState entry loop = (none,post) ∧ post.clock = source.clock - 17 ∧
        KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source ∧ post.globals = source.globals ∧
        InitializerAllocations.context post = InitializerAllocations.context source :=
    ⟨addressWalk entry pointer 0 17,address_loop_execute entry pointer 0 17 rfl binding indexBinding domain arena (by change 17 ≤ source.clock; omega),
      address_walk_clock entry pointer 0 17,address_walk_control entry pointer 0 17,address_walk_globals entry pointer 0 17,address_walk_context entry pointer 0 17⟩
  have currentInstalled := InitializerAllocations.installed_of_context source loopPost loopContext installed
  have currentDomain := (InitializerAllocations.domain_of_context source loopPost loopContext).trans domain
  have currentBinding : loopPost.globals.lookup (ofString "precompile_addrs") = some (.val (.word pointer)) := by rw [loopGlobals]; exact binding
  have destination : QueryBranch.eval loopPost (.op .add [.var .global (ofString "precompile_addrs"),.panop .mul [.const 17#64,.const 20#64],.const 18#64]) =
      some (.val (.word (byteAddress pointer 358))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,currentBinding,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,byteAddress]
  have lastByte := ByteStore.execute loopPost _ (.const 1#64) (byteAddress pointer 358) 1#8 destination rfl
    (AllocatedBytes.byte_mapped loopPost pointer 360 358 currentDomain arena (by decide))
  let bytePost := {loopPost with memory := ByteStore.put loopPost.memory loopPost.be (byteAddress pointer 358) 1#8}
  have currentHeap : bytePost.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) :=
    (congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup (ofString "heap_ptr")) loopGlobals).trans heap
  have currentScalars : OriginalScalarGlobals.Scalars bytePost.globals := loopGlobals.symm ▸ scalars
  obtain ⟨target,tailRun,upper,bounded,control⟩ := addresses_execute bytePost cursor addresses (by intro row member; exact member) currentInstalled currentScalars currentHeap currentDomain
    lower (by change cursor + (24 * 7 + 32) ≤ _; omega) aligned (by change 9 * 7 + 13 ≤ loopPost.clock; omega)
  have inner : evaluateHOLFiniteState entry (.seq loop afterLoop) = (some (.returned (.val (.word 0#64))),target) := by
    rw [StateSteps.next_sequence entry loopPost loop _ loopRun (by change loopPost.clock ≤ source.clock; omega),afterLoop,
      StateSteps.next_sequence loopPost bytePost finalByte _ lastByte (Nat.le_refl _)]
    exact tailRun
  have actual := ScalarScope.declare_execute source target "i" (.const 0#64) 0#64 (.seq loop afterLoop) (some (.returned (.val (.word 0#64)))) rfl inner
  have transported := InitializerAllocations.template_hash_control source bytePost cursor (finalActions addresses) loopControl
  refine ⟨restore source "i" target,actual,?_,?_,(scope_control target source "i").trans (control.trans transported)⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ loopPost.clock at upper
    omega
  · change source.clock - 93 ≤ target.clock
    change loopPost.clock - (9 * 7 + 13) ≤ target.clock at bounded
    omega

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.loop_tail_execute

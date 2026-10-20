import InitECandidate.Solver.Input.MainMptHashes
import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Main.MptInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem erase_hash_work (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (memory : WordWrites.Memory) (clock : Nat) :
    KeccakAbsorb.hashControl {source with memory := memory,clock := clock} = KeccakAbsorb.hashControl source := rfl

/-- Complete original MPT initialization, including both real hash calls and
their actual event/memory effects. The supplied facts concern the entry only. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 184 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 411 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 411 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (allocated source cursor) ∧
      ∀ query,Keccak256.Protected stp pad (BitVec.ofNat 64 cursor) query →
        Keccak256.Protected stp pad (BitVec.ofNat 64 (cursor + 32)) query →
        query ≠ panByteAlignHOL (width := 64) (BitVec.ofNat 64 (cursor + 128)) → post.memory query = source.memory query := by
  have allocationRun := InitializerAllocations.execute_prefix source cursor actions afterAllocation installed scalars heap valid room aligned (by change 5 ≤ source.clock; omega)
  let ready := {allocated source cursor with clock := source.clock - 5}
  let hashReady := {seeded source cursor with clock := source.clock - 5}
  have seedRun := seed_execute {source with clock := source.clock - 5} cursor environment.domain lower room aligned
  rw [allocated_clock,seeded_clock] at seedRun
  have currentControl : KeccakAbsorb.hashControl hashReady = KeccakAbsorb.hashControl (allocated source cursor) :=
    erase_hash_work (allocated source cursor) _ _
  have currentEnvironment : Keccak256.Environment hashReady stp pad :=
    (allocated_environment source cursor stp pad installed environment).of_control (allocated source cursor) hashReady stp pad currentControl
  have model : Layout hashReady cursor := (layout source cursor).of_globals (allocated source cursor) hashReady cursor
    (congrArg (fun state => state.globals) currentControl)
  obtain ⟨rootArena,hashArena,scratchArena,_⟩ := arenas cursor lower room aligned
  obtain ⟨post,hashRun,upper,bounded,control,frame⟩ := hash_tail_execute hashReady cursor installed model stp pad currentEnvironment stateArena stateAligned padArena padAligned rootArena hashArena scratchArena
    (by change 406 ≤ source.clock - 5; omega)
  have run : evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) := by
    rw [body_shape,allocationRun]
    change evaluateHOLFiniteState ready afterAllocation = _
    rw [afterAllocation,StateSteps.next_sequence ready hashReady seed _ seedRun (Nat.le_refl _)]
    exact hashRun
  refine ⟨post,run,?_,?_,control.trans currentControl,?_⟩
  · change post.clock ≤ source.clock - 5 at upper
    omega
  · change source.clock - 5 - 406 ≤ post.clock at bounded
    omega
  · intro query first second away
    exact (frame query first second).trans (ByteStore.away source.memory source.be (BitVec.ofNat 64 (cursor + 128)) query 128#8 away)

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 184 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 412 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_init") []) = (none,post) ∧ post.locals = source.locals ∧
      post.clock ≤ source.clock ∧ source.clock - 412 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (allocated source cursor) ∧
      ∀ query,Keccak256.Protected stp pad (BitVec.ofNat 64 cursor) query →
        Keccak256.Protected stp pad (BitVec.ofNat 64 (cursor + 32)) query →
        query ≠ panByteAlignHOL (width := 64) (BitVec.ofNat 64 (cursor + 128)) → post.memory query = source.memory query := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "mpt_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have entryEnvironment : Keccak256.Environment entry stp pad := environment.of_control source entry stp pad rfl
  obtain ⟨target,run,upper,bounded,control,frame⟩ := execute entry cursor installed scalars heap stp pad entryEnvironment stateArena stateAligned padArena padAligned lower room aligned (by change 411 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "mpt_init") [] [] body callee .one (.val (.word 0#64)) target rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryControl := InitializerAllocations.template_hash_control source entry cursor actions (by rfl)
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,control.trans entryControl,frame⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 412 ≤ target.clock
    change source.clock - 1 - 411 ≤ target.clock at bounded
    omega

end InitECandidate.Solver.Input.Main.MptInitialization

#print axioms InitECandidate.Solver.Input.Main.MptInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.call_execute

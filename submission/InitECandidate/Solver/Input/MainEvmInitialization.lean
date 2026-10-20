import InitECandidate.Solver.Input.MainEvmHashTail
import InitECandidate.Solver.Input.MainEvmLayout
import InitECandidate.Solver.HashEnvironmentFrame

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

private theorem restored_control (source saved target : PanSemStateFiniteExact 64 Guest.HostMemory) :
    KeccakAbsorb.hashControl (restore source "mark" (restore saved "s" target)) = KeccakAbsorb.hashControl target := rfl

private theorem combined_template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.template (InitializerAllocations.template source cursor [topicAction]) (cursor + 32)
      [systemAction,nullAction,emptyAction,keyAction,headerAction] = template source cursor := by
  simp only [template,actions,InitializerAllocations.template,topicAction,InitializerAllocations.constant]

/-- Complete original EVM startup. The temporary buffer is released before
the actual overlapping Keccak input/output call. All real hash events and
memory effects remain in the returned state. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 238 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 238 ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  let ready := topicReady source cursor
  have context := temporary_context source cursor
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentEnvironment := topic_environment source cursor stp pad installed environment
  have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query))
      [.var .local (ofString "s"),.const 33#64,.var .global (ofString "transfer_topic")] =
      some (Keccak256.values (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 cursor) 33) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,topic_binding source cursor,string_binding source cursor,Keccak256.values,ready]
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inputArena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 33 := ⟨by rw [number]; exact lower,by rw [number]; omega⟩
  have outputArena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32 := inputArena.weaken _ _ _ (by decide)
  have buffers : Keccak256.Buffers stp (BitVec.ofNat 64 cursor) pad (BitVec.ofNat 64 cursor) 33 :=
    ⟨stateArena,stateAligned,inputArena,padArena,padAligned,outputArena⟩
  obtain ⟨hashPost,hashRun,_,hashUpper,hashLower,hashControl,_⟩ := Keccak256.allocated_call ready _ stp (BitVec.ofNat 64 cursor) pad (BitVec.ofNat 64 cursor) 33
    args (Keccak256.original_code ready.code currentInstalled) currentEnvironment buffers (by change 203 ≤ source.clock - 4; omega)
  have hashGlobals : hashPost.globals = ready.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) hashControl
    exact h
  have hashCode : hashPost.code = ready.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) hashControl
    exact h
  have hashDomain : hashPost.memaddrs = ready.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) hashControl
    exact h
  have hashInstalled : OriginalCode.Installed hashPost.code := hashCode.symm ▸ currentInstalled
  have hashScalars : OriginalScalarGlobals.Scalars hashPost.globals := hashGlobals.symm ▸ temporary_scalars source cursor scalars
  have hashHeap : hashPost.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) := by
    rw [hashGlobals]
    exact topic_heap source cursor
  change source.clock - 4 - 203 ≤ hashPost.clock at hashLower
  have currentDomain : hashPost.memaddrs = InitE.ordinaryDomain := hashDomain.trans currentEnvironment.domain
  obtain ⟨tailPost,tailRun,tailClock,tailControl⟩ := after_hash_execute hashPost (cursor + 32) hashInstalled hashScalars hashHeap currentDomain
    (by omega) (by omega) (by omega) (by omega)
  have afterTopic : evaluateHOLFiniteState ready afterTopicAllocation = (some (.returned (.val (.word 0#64))),tailPost) := by
    rw [afterTopicAllocation,StateSteps.next_sequence ready hashPost topicHash afterHash hashRun hashUpper]
    exact tailRun
  let post := restore source "mark" (restore (marked source cursor) "s" tailPost)
  have actual : evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) := by
    rw [temporary_execute source cursor installed scalars heap environment.domain lower (by omega) aligned (by omega),afterTopic]
  have firstControl := (InitializerAllocations.template_hash_control ready hashPost (cursor + 32) [systemAction,nullAction,emptyAction,keyAction,headerAction] hashControl)
  have combined := InitializerAllocations.template_hash_control (InitializerAllocations.template source cursor [topicAction]) ready
    (cursor + 32) [systemAction,nullAction,emptyAction,keyAction,headerAction] (topic_control source cursor)
  refine ⟨post,actual,?_,?_,?_⟩
  · change tailPost.clock ≤ source.clock
    change hashPost.clock ≤ source.clock - 4 at hashUpper
    omega
  · change source.clock - 238 ≤ tailPost.clock
    omega
  · have completed := tailControl.trans (firstControl.trans combined)
    rw [combined_template source cursor] at completed
    exact (restored_control source (marked source cursor) tailPost).trans completed

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 239 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "evm_init") []) = (none,post) ∧ post.locals = source.locals ∧
      post.clock ≤ source.clock ∧ source.clock - 239 ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "evm_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have entryEnvironment : Keccak256.Environment entry stp pad := environment.of_control source entry stp pad rfl
  obtain ⟨target,run,upper,bounded,control⟩ := execute entry cursor installed scalars heap stp pad entryEnvironment stateArena stateAligned padArena padAligned
    lower room aligned (by change 238 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "evm_init") [] [] body callee .one (.val (.word 0#64)) target rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have model := InitializerAllocations.template_hash_control source entry cursor actions (by rfl)
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,control.trans model⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 239 ≤ target.clock
    change source.clock - 1 - 238 ≤ target.clock at bounded
    omega

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.call_execute

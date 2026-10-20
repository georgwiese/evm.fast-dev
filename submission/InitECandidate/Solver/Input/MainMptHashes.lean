import InitECandidate.Solver.Input.MainMptLayout
import InitECandidate.Solver.HashEnvironmentFrame

namespace InitECandidate.Solver.Input.Main.MptInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Both real initialization hashes execute from current allocated buffers.
Their actual memory and oracle events are retained, with no digest premise. -/
theorem hash_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (model : Layout source cursor)
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (rootArena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32)
    (hashArena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 32)) 32)
    (scratchArena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 128)) 40)
    (enough : 406 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.seq rootHash (.seq codeHash (.return (.const 0#64)))) = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 406 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source ∧
      ∀ query,Keccak256.Protected stp pad (BitVec.ofNat 64 cursor) query →
        Keccak256.Protected stp pad (BitVec.ofNat 64 (cursor + 32)) query → post.memory query = source.memory query := by
  have rootArgs : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [.var .global (ofString "mpt_hash_scratch"),.const 1#64,.var .global (ofString "empty_trie_root")] =
      some (Keccak256.values (BitVec.ofNat 64 (cursor + 128)) (BitVec.ofNat 64 cursor) 1) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,model.scratch,model.root,Keccak256.values]
  have rootBuffers : Keccak256.Buffers stp (BitVec.ofNat 64 (cursor + 128)) pad (BitVec.ofNat 64 cursor) 1 :=
    ⟨stateArena,stateAligned,AllocatedBytes.Arena.weaken _ 40 1 scratchArena (by decide),padArena,padAligned,rootArena⟩
  obtain ⟨rootPost,rootRun,_,rootUpper,rootLower,rootControl,rootFrame⟩ := Keccak256.allocated_call source _ stp (BitVec.ofNat 64 (cursor + 128)) pad (BitVec.ofNat 64 cursor) 1
    rootArgs (Keccak256.original_code source.code installed) environment rootBuffers (by change 203 ≤ source.clock; omega)
  have nextEnvironment := environment.of_control source rootPost stp pad rootControl
  have nextGlobals : rootPost.globals = source.globals := congrArg (fun s => s.globals) rootControl
  have nextCode : rootPost.code = source.code := congrArg (fun s => s.code) rootControl
  have nextModel := model.of_globals source rootPost cursor nextGlobals
  have codeArgs : evalListHOLFinite rootPost (h := fun query => Classical.propDecidable (rootPost.memaddrs query))
      [.var .global (ofString "mpt_hash_scratch"),.const 0#64,.var .global (ofString "empty_code_hash")] =
      some (Keccak256.values (BitVec.ofNat 64 (cursor + 128)) (BitVec.ofNat 64 (cursor + 32)) 0) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nextModel.scratch,nextModel.hash,Keccak256.values]
  have hashBuffers : Keccak256.Buffers stp (BitVec.ofNat 64 (cursor + 128)) pad (BitVec.ofNat 64 (cursor + 32)) 0 :=
    ⟨stateArena,stateAligned,AllocatedBytes.Arena.weaken _ 40 0 scratchArena (by decide),padArena,padAligned,hashArena⟩
  change source.clock - 203 ≤ rootPost.clock at rootLower
  obtain ⟨hashPost,hashRun,_,hashUpper,hashLower,hashControl,hashFrame⟩ := Keccak256.allocated_call rootPost _ stp (BitVec.ofNat 64 (cursor + 128)) pad (BitVec.ofNat 64 (cursor + 32)) 0
    codeArgs (Keccak256.original_code rootPost.code (by rw [nextCode]; exact installed)) nextEnvironment hashBuffers (by change 203 ≤ rootPost.clock; omega)
  change rootPost.clock - 203 ≤ hashPost.clock at hashLower
  have run : evaluateHOLFiniteState source (.seq rootHash (.seq codeHash (.return (.const 0#64)))) =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite hashPost) := by
    rw [StateSteps.next_sequence source rootPost rootHash _ rootRun rootUpper,
      StateSteps.next_sequence rootPost hashPost codeHash _ hashRun hashUpper]
    exact BuildEntry.zero_return hashPost
  exact ⟨emptyLocalsHOLFinite hashPost,run,Nat.le_trans hashUpper rootUpper,by change source.clock - 406 ≤ hashPost.clock; omega,
    hashControl.trans rootControl,fun query first second => (hashFrame query second).trans (rootFrame query first)⟩

end InitECandidate.Solver.Input.Main.MptInitialization

#print axioms InitECandidate.Solver.Input.Main.MptInitialization.hash_tail_execute

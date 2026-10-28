import InitECandidate.Solver.CurrentKeccak.Memory

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "keccak256") arguments) :=
  GlobalEffects.call_body key code (some none) _ arguments formals body .one (original_code code installed) (hash_globals key code installed)

/-- Genuine whole-hash callers retain their workspace, caller locals and
any word outside the actual state/pad/output buffers. The frame covers the
current software body and derives every normal inner phase from this call. -/
theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (inputArena : AllocatedBytes.Arena pointer length) (outArena : AllocatedBytes.Arena out 32)
    (stateAway : CopyGeneral.Away stp query 200) (padAway : CopyGeneral.Away pad query 136) (outAway : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,post)) : Frame source post stp pad query := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=Hash.environment source.code.lookup pointer out length (original_code source.code environment.installed)
  have ready : Environment (callEntryStateHOLFinite source callee) stp pad := environment.of_frame rfl
  have memory : post.memory query=source.memory query := by
    apply MemoryAt.call_normal source post _ arguments (values pointer out length) body callee .one query args called ?_ run
    intro target value bodyRun
    exact body_memory (callEntryStateHOLFinite source callee) target stp pad pointer out query length ready pointerCell countCell outCell inputArena outArena stateAway padAway outAway value bodyRun
  exact ⟨environment.after _ _ (fun key=>call_globals key source.code environment.installed arguments) run,memory,
    fun key=>CallNormal.ignored_lookup source post key (ofString "keccak256") arguments run⟩

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_globals
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_frame

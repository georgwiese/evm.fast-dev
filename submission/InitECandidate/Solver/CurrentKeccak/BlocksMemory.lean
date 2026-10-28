import InitECandidate.Solver.CurrentKeccak.Environment
import InitECandidate.Solver.Input.CounterLoopLocal

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input Input.CounterFlow WitnessRadix WitnessRadix.QueryBranch

/-- Actual block-loop iterations only write the software state region.
The real counter and byte-count are propagated from each continuing body. -/
theorem blocks_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer query : BitVec 64) (length : Nat)
    (small : length+136<2^64) (installed : OriginalCode.Installed source.code)
    (valid : StrideInvariant length source)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (stateCell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source blocks=(none,post)) : post.memory query=source.memory query := by
  let invariant:=fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>StrideInvariant length state ∧
    state.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ state.locals.lookup (ofString "stp")=some (.val (.word stp))
  apply MemoryAt.loop_normal source.code (ofString "n") condition blockBody query (fun current=>block_safe.summary_full current) invariant ?_
    source post rfl ⟨valid,pointerCell,stateCell⟩ run
  intro current codeEq ready observed read nonzero funded target bodyRun
  have next:=(stride_transition condition blockBody 136 length (by decide) (by omega) block_advance block_safe.summary_full (test_reads length small)
    current ready.1 observed read nonzero).2 funded
  rw [bodyRun] at next
  have nextCounter:=(next (Or.inl rfl)).1
  have keep (key : MlS) (different : key≠ofString "i") : target.locals.lookup key=current.locals.lookup key := by
    have safe : LocalPrefix key blockBody := .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)
    have summary:=safe.summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    rw [bodyRun] at summary
    exact summary.1 rfl
  have nextInvariant : invariant target := ⟨nextCounter,(keep _ (by decide)).trans ready.2.1,(keep _ (by decide)).trans ready.2.2⟩
  obtain ⟨index,indexCell,countCell,bounded⟩:=ready.1
  obtain ⟨middle,front,back⟩:=Input.sequence_none (decClockHOLFinite current) target _ _ bodyRun
  have args : evalListHOLFinite (decClockHOLFinite current) (h:=fun address=>Classical.propDecidable ((decClockHOLFinite current).memaddrs address)) blockArguments=
      some (Absorb.values stp (pointer+index)) := by
    simp [blockArguments,Absorb.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,decClockHOLFinite,decClockHOLExact,localVar,
      ready.2.1,ready.2.2,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actualInstalled : OriginalCode.Installed (decClockHOLFinite current).code := by
    change OriginalCode.Installed current.code
    rw [codeEq]
    exact installed
  have first:=Absorb.call_memory (decClockHOLFinite current) middle stp (pointer+index) query actualInstalled blockArguments args away front
  have last:=LocalEffects.assign middle.code (ofString "i") (.op .add [localVar "i",.const 136#64]) middle rfl
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 136#64]))=(none,target) at back
  rw [back] at last
  exact ⟨nextInvariant,(congrFun (LocalEffects.memory_of_erase middle target last) query).trans first⟩

/-- Hash-loop callers retain all pointer bindings while the local counter advances. -/
theorem blocks_local (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS) (different : key≠ofString "i")
    (run : evaluateHOLFiniteState source blocks=(none,post)) : post.locals.lookup key=source.locals.lookup key :=
  Input.counter_loop_local source post condition (ofString "keccak_absorb_block") blockArguments "i" (.op .add [localVar "i",.const 136#64]) key different run

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_memory
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_local

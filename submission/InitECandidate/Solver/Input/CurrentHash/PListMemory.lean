import InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory
import InitECandidate.Solver.Input.CurrentHash.MixMemory
import InitECandidate.Solver.Input.CurrentHash.PListCost

namespace InitECandidate.Solver.Input.CurrentHash.PListMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open PListCost

theorem tail_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (chunk out query : BitVec 64)
    (data : MixMemory.Params source chunk out) (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source tail=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") := by
  have pure : GlobalEffects.Preserves (ofString "heap_ptr") source.code tail := GlobalEffects.sequence (ofString "heap_ptr") source.code _ _
    (PureGlobals.mix_call _ source.code data.installed (some none) _) (GlobalEffects.returned _ source.code _)
  have globals := pure source rfl
  change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source tail).2=_ at globals
  rw [actual] at globals
  unfold tail at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .mix_in_length) [localVar "out",localVar "len",localVar "out"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (localVar "out")=some (.val (.word out)) := by
    simpa [evalHOLFinite,evalHOLExact,toExact,localVar] using data.output
  have mixed := MixMemory.call_output_memory source middle (localVar "out") (localVar "len") (localVar "out") chunk out query data.installed data.domain
    data.chunkCell chunkArena chunkAligned chunkAway outAway read normal
  have memory := MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at memory
  exact ⟨memory.trans mixed,congrArg Prod.snd globals⟩

/-- Progressive list hashing retains metadata outside its actual length chunk
and output, restoring the entering heap. The length word is unrestricted. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (Code.body .htr_plist_chunks)=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Progressive.values roots (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arguments,localVar,pointer,count,output,Progressive.values,CallNormal.tripleValues]
  rw [source_shape] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize_progressive") arguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have image := ProgressiveMemory.call_frame source middle roots cursor out zeros query n context bounded inputArena outArena outAway arguments args normal
  have data : MixMemory.Params source chunk out := ⟨context.installed,context.domain,chunkCell,output⟩
  have next := data.after_call (ofString "merkleize_progressive") arguments (Effects.call_preserves .lengthChunk source.code context.installed .merkleize_progressive (some none) _) normal
  have ending := tail_frame middle post chunk out query next chunkArena chunkAligned chunkAway outAway value remaining
  exact ⟨ending.1.trans image.1,ending.2.trans image.2⟩

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor len chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728)
    (inputArena : AllocatedBytes.Arena roots (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values roots len out n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .htr_plist_chunks) expressions)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pointer,count,output⟩ := environment source.code context.installed roots len out n
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name .htr_plist_chunks) expressions actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame (callEntryStateHOLFinite source callee) target roots cursor chunk out zeros query n (context.at_callee callee) bounded
    pointer count output inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.PListMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.PListMemory.tail_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PListMemory.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PListMemory.call_frame

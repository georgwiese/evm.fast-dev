import InitECandidate.Solver.Input.CurrentHash.PayloadFinalCost
import InitECandidate.Solver.Input.CurrentHash.PContainerMemory

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem container_tail_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch cursor out zeros query : BitVec 64)
    (context : MerkleMemory.Context source cursor zeros query)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena ch 608) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source containerTail=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.containerArguments=
      some [.val (.word ch),.val (.word 19#64),.val (.word out)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,StaticFields.containerArguments,localVar,chunks,output]
  have safe : LocalPrefix (ofString "ch") (.call (some (none,none)) (ofString "htr_pcontainer") StaticFields.containerArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold containerTail at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := PContainer.call_frame source middle ch cursor out zeros query 19 context (by decide) inputArena outAway StaticFields.containerArguments args normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact context.installed
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans frame.1

theorem State.after_balance_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterBalance=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold afterBalance at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((StaticFields.step_local (.scalar 532 18) (ofString "ch")).summary_full source).2.1 actual
  have shape := StaticFields.fields_geometry (blob+62#64) ch query (.scalar 532 18) (by simp [StaticFields.lastFields])
    (raw_arena data.decoded data.inputBound data.inputArena) data.chunksArena data.chunksAligned before
  have frame := StaticFields.step_frame (.scalar 532 18) source middle (blob+62#64) ch cursor zeros query (by trivial) (data.query_context query before)
    data.raw data.chunks shape.1 shape.2.1 shape.2.2.1 shape.2.2.2 normal
  have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "htr_u64_at") (StaticFields.arguments (.scalar 532 18)) normal
  exact (container_tail_memory middle post ch cursor out zeros query frame.2 ((kept "ch").trans data.chunks) ((kept "out").trans data.output)
    data.chunksArena outAway value remaining).trans frame.1

theorem State.after_final_scalars_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterFinalScalars=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "ch") (.call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold afterFinalScalars at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := data.balance_frame query before chunkAway normal
  have next := data.after_balance normal
  exact (next.after_balance_memory query before outAway value remaining).trans frame.1

/-- Complete current final payload phase: scalar fields, real balance bytes,
actual nineteen-field activity mask/container and saved-mark release. -/
theorem State.final_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source finalFields=(some (.returned value),post)) : post.memory query=source.memory query := by
  have members : ∀ field∈([.scalar 512 15,.scalar 520 16] : List StaticFields.Field),field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields := by
    intro field member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> simp [StaticFields.lastFields]
  rw [StaticFields.final_shape] at actual
  change evaluateHOLFiniteState source (StaticFields.program [.scalar 512 15,.scalar 520 16] afterFinalScalars)=(some (.returned value),post) at actual
  apply StaticFields.program_memory [.scalar 512 15,.scalar 520 16] afterFinalScalars source post (blob+62#64) ch cursor zeros query
    (by intro field member; exact (StaticFields.fields_valid field (members field member)).1) (data.query_context query before) data.raw data.chunks
    (by intro field member; exact StaticFields.fields_geometry _ _ _ field (members field member) (raw_arena data.decoded data.inputBound data.inputArena) data.chunksArena data.chunksAligned before)
    _ value actual
  intro middle ready normal observed returned
  exact (data.after_static _ members normal).after_final_scalars_memory query before chunkAway outAway observed returned

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.container_tail_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_balance_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_final_scalars_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.final_memory

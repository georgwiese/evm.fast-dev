import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionScopeMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadPrefixCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.middle_fields_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (StaticFields.program StaticFields.middleFields transactionScope)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  have members : ∀ field∈StaticFields.middleFields,field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields := by intro field member; simp [member]
  apply StaticFields.program_memory StaticFields.middleFields transactionScope source post (blob+62#64) ch cursor zeros query
    (by intro field member; exact (StaticFields.fields_valid field (members field member)).1) (data.query_context query before) data.raw data.chunks
    (by intro field member; exact StaticFields.fields_geometry _ _ _ field (members field member) (raw_arena data.decoded data.inputBound data.inputArena) data.chunksArena data.chunksAligned before)
    _ value actual
  intro middle ready normal observed returned
  have next := data.after_static (post:=middle) StaticFields.middleFields members normal
  exact next.transaction_memory (post:=post) query before chunkAway outAway observed returned

theorem State.after_first_fields_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterFirstFields=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold afterFirstFields at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := data.extra_frame query before chunkAway normal
  have next := data.after_extra (post:=middle) normal
  exact (next.middle_fields_memory (post:=post) query before chunkAway outAway value remaining).trans frame.1

/-- Complete current payload continuation after the actual chunk allocation,
including both dynamic phases, retains arbitrary earlier protected metadata. -/
theorem State.prefix_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source PayloadHash.afterChunks=(some (.returned value),post)) : post.memory query=source.memory query := by
  have members : ∀ field∈StaticFields.firstFields,field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields := by intro field member; simp [member]
  rw [StaticFields.prefix_shape] at actual
  change evaluateHOLFiniteState source (StaticFields.program StaticFields.firstFields afterFirstFields)=(some (.returned value),post) at actual
  apply StaticFields.program_memory StaticFields.firstFields afterFirstFields source post (blob+62#64) ch cursor zeros query
    (by intro field member; exact (StaticFields.fields_valid field (members field member)).1) (data.query_context query before) data.raw data.chunks
    (by intro field member; exact StaticFields.fields_geometry _ _ _ field (members field member) (raw_arena data.decoded data.inputBound data.inputArena) data.chunksArena data.chunksAligned before)
    _ value actual
  intro middle ready normal observed returned
  have next := data.after_static (post:=middle) StaticFields.firstFields members normal
  exact next.after_first_fields_memory (post:=post) query before chunkAway outAway observed returned

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.middle_fields_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_first_fields_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.prefix_memory

import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalSuffixCost
import InitECandidate.Solver.Input.CurrentHash.PayloadFinalMemory

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.after_withdrawal_list_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (query : BitVec 64) (before : query.toNat<ch.toNat)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterWithdrawalList=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [withdrawal_shapes.2.2.2.2.2.2] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "heap_release") [localVar "m2"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have next := data.released "m2" base saved.binding saved.lower saved.upper saved.aligned saved.afterChunks normal
  have memory := HeapScope.ignored_release_memory source middle [localVar "m2"] data.context.installed normal
  exact (next.final_memory query before chunkAway outAway value remaining).trans (congrFun memory query)

theorem State.after_withdrawal_loop_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n)))) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterWithdrawalLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [withdrawal_shapes.2.2.2.2.2.1] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments "nwd" 14)) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := data.list_frame "nwd" 14 n roots query bounded (by decide) root count rootsArena before chunkAway normal
  have next := data.after_list "nwd" 14 n roots bounded (by decide) root count rootsArena normal
  have kept := saved.after_call _ _ normal
  exact (next.after_withdrawal_list_memory kept query before chunkAway outAway value remaining).trans frame.1

/-- Real withdrawal loop, actual following root list, releases and final
payload fields preserve arbitrary protected caller metadata, including words
outside the payload record itself. -/
theorem State.withdrawal_loop_suffix_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p roots : BitVec 64) (n index : Nat)
    (round : Withdrawals.RoundState source p roots n index) (bounded : n≤134217728) (inside : index≤n)
    (inputArena : AllocatedBytes.Arena p (44*n)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAligned : roots.toNat%8=0) (rootsAfter : ch.toNat≤roots.toNat)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source withdrawalLoopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [withdrawal_shapes.2.2.2.2.1] at actual
  have safe : LocalPrefix (ofString "m2") withdrawalLoop := by rw [loop_shapes.2.2.1]; exact .loop _ (withdrawal_step_local _ (by decide))
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := Withdrawals.loop_frame source middle p roots cursor zeros query n index (data.query_context query before) round bounded inside inputArena rootsArena
    (CopyGeneral.Away.after roots query (32*n) rootsAligned (by have h:=rootsArena.upper; omega) (by omega)) normal
  obtain ⟨next,position,positionBound,nextRound⟩ := data.after_withdrawal_loop p roots n index round bounded inside inputArena rootsArena rootsAligned rootsAfter normal
  have kept := saved.after_program withdrawalLoop safe normal
  exact (next.after_withdrawal_loop_memory kept roots n bounded nextRound.root nextRound.count rootsArena query before chunkAway outAway value remaining).trans frame.1

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_withdrawal_list_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_withdrawal_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_loop_suffix_memory

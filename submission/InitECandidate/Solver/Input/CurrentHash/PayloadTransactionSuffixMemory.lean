import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionSuffixCost
import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalScopeMemory

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.after_transaction_list_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (query : BitVec 64) (before : query.toNat<ch.toNat)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterTransactionList=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [transaction_shapes.2.2.2.2.2.2.2] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "heap_release") [localVar "m2"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have next := data.released "m2" base saved.binding saved.lower saved.upper saved.aligned saved.afterChunks normal
  have memory := HeapScope.ignored_release_memory source middle [localVar "m2"] data.context.installed normal
  have kept := saved.after_call _ _ normal
  exact (next.withdrawal_memory kept query before chunkAway outAway value remaining).trans (congrFun memory query)

theorem State.after_transaction_loop_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size))
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterTransactionLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  have bounded := data.transaction_data.2.2
  rw [transaction_shapes.2.2.2.2.2.2.1] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments "ntx" 13)) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := data.list_frame "ntx" 13 _ roots query bounded (by decide) root count rootsArena before chunkAway normal
  have next := data.after_list "ntx" 13 _ roots bounded (by decide) root count rootsArena normal
  have kept := saved.after_call _ _ normal
  exact (next.after_transaction_list_memory kept query before chunkAway outAway value remaining).trans frame.1

/-- Current transaction loop and its actual following list/release and
complete withdrawal phase retain arbitrary protected earlier caller metadata. -/
theorem State.transaction_loop_suffix_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64) (index : Nat)
    (round : Transactions.RoundState source (VarList.decodedArray array size) roots cursor chunk zeros (Transactions.decodedPointers input blob start)
      (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) index)
    (inside : index≤VarList.decodedCount input start size)
    (geometry : Transactions.Geometry (VarList.decodedArray array size) roots cursor chunk (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
      (VarList.decodedCount input start size) size) (rootsAfter : ch.toNat≤roots.toNat)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source transactionLoopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [transaction_shapes.2.2.2.2.2.1] at actual
  have safe : LocalPrefix (ofString "m2") transactionLoop := by rw [loop_shapes.1]; exact .loop _ (transaction_step_local _ (by decide))
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := Transactions.loop_frame source middle (VarList.decodedArray array size) roots cursor chunk zeros query (Transactions.decodedPointers input blob start)
    (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) size index round geometry inside (by have h:=data.afterChunks; omega)
    (CopyGeneral.Away.after roots query _ geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) (by omega)) chunkAway normal
  obtain ⟨next,position,positionBound,nextRound⟩ := data.after_transaction_loop roots index round inside geometry rootsAfter normal
  have kept := saved.after_program transactionLoop safe normal
  exact (next.after_transaction_loop_memory kept roots nextRound.rootsLocal nextRound.count geometry.rootsArena query before chunkAway outAway value remaining).trans frame.1

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_transaction_list_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_transaction_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_loop_suffix_memory

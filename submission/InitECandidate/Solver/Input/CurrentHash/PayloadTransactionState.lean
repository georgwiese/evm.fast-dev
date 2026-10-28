import InitECandidate.Solver.Input.CurrentHash.PayloadStateTransport
import InitECandidate.Solver.Input.CurrentHash.PayloadDynamicList

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.transaction_data (data : State input source blob record array ch cursor chunk out zeros length start size) :
    eval source (fieldExpression 32)=some (.val (.word (VarList.decodedArray array size))) ∧
    eval source (fieldExpression 40)=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))) ∧ VarList.decodedCount input start size≤134217728 := by
  have cells := data.decoded.transactions.records.cells source input blob array start size data.context.domain
  have slice := data.decoded.transactions.inside
  have bound := data.inputBound
  exact ⟨data.field_read 32 (by decide) (by decide) _ data.decoded.transactions.txs,
    data.field_read 40 (by decide) (by decide) _ data.decoded.transactions.count,by omega⟩

theorem State.transaction_round (data : State input source blob record array ch cursor chunk out zeros length start size) (roots : BitVec 64) (index : Nat)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    Transactions.RoundState source (VarList.decodedArray array size) roots cursor chunk zeros (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
      (VarList.decodedCount input start size) index := by
  have below : (VarList.decodedArray array size).toNat<cursor.toNat := by
    by_cases empty : size=0
    · simp only [VarList.decodedArray,if_pos empty]
      have h:=data.context.heapLower
      change 0<cursor.toNat
      omega
    · simp only [VarList.decodedArray,if_neg empty]
      have a:=data.afterArray; have b:=data.afterChunks
      omega
  have context : MerkleMemory.Context source cursor zeros (VarList.decodedArray array size) := ⟨data.context.installed,data.context.domain,data.context.zeroCell,
    data.context.zeroArena,data.context.heap,data.context.heapLower,data.context.heapBound,data.context.aligned,below⟩
  exact ⟨context,pointer,count,root,position,Transactions.decoded_image source input blob array start size data.context.domain data.decoded.transactions.records,data.chunkCell⟩

theorem State.transaction_geometry (data : State input source blob record array ch cursor chunk out zeros length start size) (roots : BitVec 64)
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size)) (rootsAligned : roots.toNat%8=0)
    (rootsAfter : ch.toNat≤roots.toNat) (rootsBefore : roots.toNat+32*VarList.decodedCount input start size≤cursor.toNat) :
    Transactions.Geometry (VarList.decodedArray array size) roots cursor chunk (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
      (VarList.decodedCount input start size) size :=
  Transactions.decoded_geometry source input blob array roots cursor chunk start size data.context.domain data.decoded.transactions.records
    (by have a:=data.decoded.transactions.inside; have b:=data.inputBound; omega) (by have h:=data.afterArray; omega)
    (by have a:=data.chunkBefore; have b:=data.decoded.transactions.arrayAfter; omega)
    data.chunkArena data.chunkAligned rootsArena rootsAligned rootsBefore

/-- The current transaction loop retains the complete earlier payload, not
just its transaction rows, before the next actual list call. -/
theorem State.after_transaction_loop (data : State input source blob record array ch cursor chunk out zeros length start size) (roots : BitVec 64) (index : Nat)
    (round : Transactions.RoundState source (VarList.decodedArray array size) roots cursor chunk zeros (Transactions.decodedPointers input blob start)
      (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) index)
    (inside : index≤VarList.decodedCount input start size)
    (geometry : Transactions.Geometry (VarList.decodedArray array size) roots cursor chunk (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
      (VarList.decodedCount input start size) size) (rootsAfter : ch.toNat≤roots.toNat)
    (actual : evaluateHOLFiniteState source transactionLoop=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size ∧
      Transactions.valid (VarList.decodedArray array size) roots cursor chunk zeros (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size)
        (VarList.decodedCount input start size) post := by
  have frame (query : BitVec 64) (lower : record.toNat≤query.toNat) (before : query.toNat<ch.toNat) := Transactions.loop_frame source post (VarList.decodedArray array size) roots cursor chunk zeros query
    (Transactions.decodedPointers input blob start) (Transactions.decodedLengths input start size) (VarList.decodedCount input start size) size index round geometry inside
    (by have h:=data.afterChunks; omega)
    (CopyGeneral.Away.after roots query _ geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) (by omega)) (data.chunk_away query lower) actual
  have atRecord := frame record (Nat.le_refl _) (by have h:=data.afterRecord; omega)
  obtain ⟨position,positionBound,nextRound⟩ := atRecord.2
  have context : MerkleMemory.Context post cursor zeros record := ⟨nextRound.context.installed,nextRound.context.domain,nextRound.context.zeroCell,nextRound.context.zeroArena,
    nextRound.context.heap,nextRound.context.heapLower,nextRound.context.heapBound,nextRound.context.aligned,data.context.below⟩
  have kept (name : String) (different : ofString name≠ofString "i") : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (LocalPrefix.loop transactionTest (transaction_step_local (ofString name) different)).summary_full source
    unfold LocalSummary at summary
    rw [←loop_shapes.1,actual] at summary
    exact summary.1 rfl
  refine ⟨?_,position,positionBound,nextRound⟩
  exact data.with_context cursor context data.afterChunks (by intro query lower before; exact (frame query lower before).1)
    ((kept "pl" (by decide)).trans data.payload) ((kept "raw" (by decide)).trans data.raw) ((kept "ch" (by decide)).trans data.chunks)
    ((kept "out" (by decide)).trans data.output) nextRound.chunkCell

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_data
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_round
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_geometry
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_transaction_loop

import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalSuffixMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalAllocationCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.withdrawal_reset_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p roots : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))) (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n))))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots))) (inputArena : AllocatedBytes.Arena p (44*n))
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAligned : roots.toNat%8=0) (rootsAfter : ch.toNat≤roots.toNat)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterWithdrawalAllocation=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [withdrawal_shapes.2.2.2.1] at actual
  have safe : LocalPrefix (ofString "nwd") (.assign .local (ofString "i") (.const 0#64)) := .assign _ _ (by decide)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have endpoint := assign_none source middle "i" (.const 0#64) 0#64 rfl normal
  have next := data.bound "i" 0#64 (by decide)
  have nextSaved : SavedCursor (bind source "i" 0#64) "m2" ch base := saved.of_lookup ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved.binding)
  have round : Withdrawals.RoundState (bind source "i" 0#64) p roots n 0 := ⟨next.context.installed,
    (bind_lookup_other source "i" "wd" 0#64 (by decide)).trans pointer,
    (bind_lookup_other source "i" "roots" 0#64 (by decide)).trans root,
    (bind_lookup_other source "i" "nwd" 0#64 (by decide)).trans count,bind_lookup_same source "i" 0#64⟩
  rw [endpoint] at remaining
  exact next.withdrawal_loop_suffix_memory (post:=post) nextSaved p roots n 0 round bounded (by omega) inputArena rootsArena rootsAligned rootsAfter query before chunkAway outAway value remaining

/-- Same real assigned allocation supplies its own room/root arena and
preserves arbitrary caller memory before the remaining withdrawal phase. -/
theorem State.withdrawal_after_nwd_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (p : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))) (count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n))))
    (inputArena : AllocatedBytes.Arena p (44*n))
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterNwd=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [withdrawal_shapes.2.2.1] at actual
  have safe : LocalPrefix (ofString "nwd") (.call (some (some (.local,ofString "roots"),none)) (ofString "alloc") (rootsAllocationArguments "nwd")) :=
    .call (some (ofString "roots")) _ _ (by intro name equal; cases equal; decide)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  let amount := BitVec.ofNat 64 (32*n+32)
  have allocation := AssignedAllocation.normal source middle cursor amount data.context.installed data.context.heap data.context.heapBound "roots" (rootsAllocationArguments "nwd")
    (roots_arguments_read source "nwd" n count) normal
  have kept := allocation.2.2.1
  have ready := data.allocated amount allocation.1 allocation.2.2.2
  have next : State input middle blob record array ch (PersistentAlloc.rounded cursor amount) chunk out zeros length start size := ready.of_frame rfl
    ((kept (ofString "pl") (by decide)).trans data.payload) ((kept (ofString "raw") (by decide)).trans data.raw)
    ((kept (ofString "ch") (by decide)).trans data.chunks) ((kept (ofString "out") (by decide)).trans data.output)
  have nextSaved : SavedCursor middle "m2" ch base := saved.of_lookup ((kept (ofString "m2") (by decide)).trans saved.binding)
  have number : amount.toNat=32*n+32 := roots_amount_number n bounded
  have rootsArena : AllocatedBytes.Arena cursor (32*n) := ⟨data.context.heapLower,by have h:=allocation.1; rw [number] at h; omega⟩
  have memory : middle.memory=source.memory := LocalEffects.memory_of_erase (PersistentAlloc.post source cursor amount) middle allocation.2.2.2
  have frame := next.withdrawal_reset_memory (post:=post) nextSaved p cursor n bounded ((kept (ofString "wd") (by decide)).trans pointer)
    ((kept (ofString "nwd") (by decide)).trans count) allocation.2.1 inputArena rootsArena data.context.aligned (by have h:=data.afterChunks; omega)
    query before chunkAway outAway value remaining
  exact frame.trans (congrFun memory query)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_reset_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_after_nwd_memory

import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionSuffixMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionAllocationCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

theorem State.transaction_i_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (roots : BitVec 64)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size)) (rootsAligned : roots.toNat%8=0)
    (rootsAfter : ch.toNat≤roots.toNat) (rootsBefore : roots.toNat+32*VarList.decodedCount input start size≤cursor.toNat)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterTxRoots=(some (.returned value),post)) : post.memory query=source.memory query := by
  let entry := bind source "i" 0#64
  have next : State input entry blob record array ch cursor chunk out zeros length start size := data.bound "i" 0#64 (by decide)
  have nextSaved : SavedCursor entry "m2" ch base := saved.of_lookup ((bind_lookup_other source "i" "m2" 0#64 (by decide)).trans saved.binding)
  have round := next.transaction_round roots 0 ((bind_lookup_other source "i" "txs" 0#64 (by decide)).trans pointer)
    ((bind_lookup_other source "i" "ntx" 0#64 (by decide)).trans count) ((bind_lookup_other source "i" "roots" 0#64 (by decide)).trans root) (bind_lookup_same source "i" 0#64)
  have geometry := next.transaction_geometry roots rootsArena rootsAligned rootsAfter rootsBefore
  let output := evaluateHOLFiniteState entry transactionLoopAndSuffix
  have whole := ScalarScope.declare_execute source output.2 "i" (.const 0#64) 0#64 transactionLoopAndSuffix output.1 rfl rfl
  rw [←transaction_shapes.2.2.2.2.1] at whole
  have resultEq : some (.returned value)=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have memoryEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.memory query) (actual.symm.trans whole)
  change post.memory query=output.2.memory query at memoryEq
  have returned : evaluateHOLFiniteState entry transactionLoopAndSuffix=(some (.returned value),output.2) := Prod.ext resultEq.symm rfl
  have frame := next.transaction_loop_suffix_memory (post:=output.2) nextSaved roots 0 round (by omega) geometry rootsAfter query before chunkAway outAway value returned
  change output.2.memory query=source.memory query at frame
  exact memoryEq.trans frame

/-- The actual transaction-root allocation supplies its own room and exact
continuation state before protected-memory reasoning enters the real loop. -/
theorem State.transaction_after_second_mark_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base)
    (pointer : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterSecondMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have bounded := data.transaction_data.2.2
  let amount := BitVec.ofNat 64 (32*VarList.decodedCount input start size+32)
  have number : amount.toNat=32*VarList.decodedCount input start size+32 := roots_amount_number _ bounded
  rw [transaction_shapes.2.2.2.1] at actual
  obtain ⟨room,funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "roots" (rootsAllocationArguments "ntx") afterTxRoots cursor amount
    (roots_arguments_read source "ntx" _ count) (PersistentAlloc.original_code source.code data.context.installed) (Trap.original_code source.code data.context.installed)
    data.context.heap data.context.heapBound value actual
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} cursor amount
  let entry := MemoryContextAllocation.entry source cursor amount "roots"
  have next : State input entry blob record array ch (PersistentAlloc.rounded cursor amount) chunk out zeros length start size := data.allocated (post:=allocated) amount room rfl
  have kept (name : String) (different : ofString "roots"≠ofString name) := CallNormal.continuation_lookup_other source allocated "roots" name (.val (.word cursor)) different
  have nextSaved : SavedCursor entry "m2" ch base := saved.of_lookup ((kept "m2" (by decide)).trans saved.binding)
  have rootsArena : AllocatedBytes.Arena cursor (32*VarList.decodedCount input start size) := ⟨data.context.heapLower,by rw [number] at room; omega⟩
  have guards := PersistentAlloc.guards cursor amount room
  have frame := next.transaction_i_memory (post:=inner) nextSaved cursor ((kept "txs" (by decide)).trans pointer) ((kept "ntx" (by decide)).trans count)
    (CallNormal.continuation_lookup_same source allocated "roots" (.val (.word cursor))) rootsArena data.context.aligned (by have h:=data.afterChunks; omega)
    (by have h:=guards.2.2.1; rw [number] at h; omega) query before chunkAway outAway value remaining
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_i_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.transaction_after_second_mark_memory

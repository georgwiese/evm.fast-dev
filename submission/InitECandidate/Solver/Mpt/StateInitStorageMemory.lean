import InitECandidate.Solver.Mpt.StateInitStorageNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

/-- Every old word except the actual ws+32 field survives the real
storage-table constructor and its exact pointer store. -/
theorem storage_old_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap query : BitVec 64)
    (valid : NaturalLayout.Valid .word (NaturalLayout.fresh .word heap.toNat 64))
    (before : query.toNat<heap.toNat) (away : query≠workspace+32#64) :
    (storageReady source workspace heap).memory query=source.memory query :=
  (if_neg away).trans (TableRuntime.caller_memory_away source "t" .word heap.toNat 64 valid query (Or.inl before))

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.storage_old_word

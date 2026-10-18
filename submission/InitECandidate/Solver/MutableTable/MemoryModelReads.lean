import InitECandidate.Solver.MutableTable.MemoryModel

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Evaluate an original table-header load from its physical representation. -/
theorem Header.read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64) (header : Header source.memory kind plan count)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) (word : BitVec 64) (member : (offset, word) ∈ headerEntries kind plan count) :
    eval source (Find.tableLoad (BitVec.ofNat 64 offset)) = some (.val (.word word)) := by
  apply Find.table_read source _ _ word tableLocal
  · rw [domain, constant_cell]
    exact mapped kind plan valid .header offset inside aligned
  · rw [constant_cell]
    exact header offset word member

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Header.read

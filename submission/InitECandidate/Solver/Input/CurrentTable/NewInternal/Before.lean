import InitECandidate.Solver.Input.CurrentTable.NewInternal.Memory

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem model_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit query : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (before : query.toNat < table.toNat) :
    (model source table cap node bit).memory query = source.memory query := by
  rw [model,stored,node_before _ table cap node bit query 24 geometry inside (by decide) before,
    node_before _ table cap node 0#64 query 16 geometry inside (by decide) before,
    node_before _ table cap node 0#64 query 8 geometry inside (by decide) before,
    node_before _ table cap node 0#64 query 0 geometry inside (by decide) before]
  have number := byteAddress_toNat table 64 (by have := geometry.table.upper; omega)
  change (table+64#64).toNat = table.toNat+64 at number
  have away : query ≠ table+64#64 := by
    intro same
    have equal := congrArg BitVec.toNat same
    rw [number] at equal
    omega
  simp only [New.putField,StoreWord.put,if_neg away]

end InitECandidate.Solver.Input.CurrentTable.NewInternal

#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_before

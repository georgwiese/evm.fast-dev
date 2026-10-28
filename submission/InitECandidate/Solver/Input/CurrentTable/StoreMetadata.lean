import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.CurrentTable.NodeStores
import InitECandidate.Solver.Input.CurrentTable.KeyCopy

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact

theorem node_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node value : BitVec 64) (offset : Nat) :
    MemoryMetadata.erase (putNode source base node offset value) = MemoryMetadata.erase source := rfl

theorem header_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (field : Nat) :
    MemoryMetadata.erase (New.putField source table field value) = MemoryMetadata.erase source := rfl

theorem copy_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer target : BitVec 64) :
    MemoryMetadata.erase (KeyCopy.result source pointer target) = MemoryMetadata.erase source := rfl

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.node_metadata
#print axioms InitECandidate.Solver.Input.CurrentTable.copy_metadata

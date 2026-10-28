import InitECandidate.Solver.Input.CurrentTable.NewLeaf.NoGrow
import InitECandidate.Solver.Input.CurrentTable.StoreMetadata

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact

theorem putField_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (offset : Nat) :
    (New.putField source table offset value).memaddrs = source.memaddrs := rfl

theorem NewLeaf.order_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pos node : BitVec 64) :
    MemoryMetadata.erase (putOrder source table cap pos node) = MemoryMetadata.erase source := rfl

theorem NewLeaf.model_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    MemoryMetadata.erase (model source table cap node pos pointer value) = MemoryMetadata.erase source := by
  simp only [model,stored,tailStored,header_metadata,order_metadata,node_metadata,copy_metadata]

theorem NewLeaf.model_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).memaddrs = source.memaddrs := MemoryMetadata.domain (model_metadata source table cap node pos pointer value)

theorem NewLeaf.model_endian (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).be = source.be := MemoryMetadata.endian (model_metadata source table cap node pos pointer value)

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_domain

import InitECandidate.Solver.Input.CurrentTable.EarlierKey
import InitECandidate.Solver.Input.CurrentTable.NodeFrames
import InitECandidate.Solver.Input.CurrentTable.StoreMetadata

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem node_earlier_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node value pointer : BitVec 64) (offset : Nat) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (small : offset < 32)
    (before : pointer.toNat+32 ≤ table.toNat) (view : FirstDiff.ByteView source pointer key) :
    FirstDiff.ByteView (putNode source (New.nodesPointer table cap) node offset value) pointer key := by
  have metadata := node_metadata source (New.nodesPointer table cap) node value offset
  exact view.before_frame table.toNat (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
    (fun query earlier => node_before source table cap node value query offset geometry inside small earlier)
    (by have := geometry.table.upper; omega) before

theorem header_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value query : BitVec 64) (field : Nat)
    (arena : AllocatedBytes.Arena table 88) (small : field < 88) (before : query.toNat < table.toNat) :
    (New.putField source table field value).memory query = source.memory query := by
  have number := byteAddress_toNat table field (by have := arena.upper; omega)
  change (table+BitVec.ofNat 64 field).toNat = table.toNat+field at number
  have away : query ≠ table+BitVec.ofNat 64 field := by
    intro same
    have equal := congrArg BitVec.toNat same
    rw [number] at equal
    omega
  simp only [New.putField,StoreWord.put,if_neg away]

theorem header_earlier_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value pointer : BitVec 64) (field : Nat) (key : KeyBits.Key)
    (arena : AllocatedBytes.Arena table 88) (small : field < 88) (before : pointer.toNat+32 ≤ table.toNat)
    (view : FirstDiff.ByteView source pointer key) : FirstDiff.ByteView (New.putField source table field value) pointer key := by
  have metadata := header_metadata source table value field
  exact view.before_frame table.toNat (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
    (fun query earlier => header_before source table value query field arena small earlier)
    (by have := arena.upper; omega) before

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.node_earlier_key
#print axioms InitECandidate.Solver.Input.CurrentTable.header_earlier_key

import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Returned
import InitECandidate.Solver.Mpt.WitnessCoreLoopFields

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack PanSemStateFiniteExact

/-- A real decoder/lookup allocation stage preserves the complete earlier
current Patricia database at the actual persistent frontier. -/
theorem Database.of_live_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {data : NodeBuild.Data}
    (database : Database source data) (heap cursor limit : BitVec 64)
    (before : (New.endPointer data.table data.cap).toNat≤heap.toNat)
    (frame : Mpt.WitnessDecode.LiveFrame source target heap cursor limit) : Database target data :=
  database.of_before heap.toNat before frame.domain frame.endian frame.memoryBefore

/-- The resolver's actual scratch HASH store also preserves every earlier
row and Patricia cell. This consumes the whole phase's genuine frame. -/
theorem Database.of_database_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {data : NodeBuild.Data}
    (database : Database source data) (heap : BitVec 64)
    (before : (New.endPointer data.table data.cap).toNat≤heap.toNat)
    (frame : Mpt.WitnessCore.DatabaseFrame source target heap) : Database target data :=
  database.of_before heap.toNat before frame.domain frame.endian frame.memory

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.Database.of_live_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.Database.of_database_frame

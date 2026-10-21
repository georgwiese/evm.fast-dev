import InitECandidate.Solver.Mpt.StateInitPrefixFields
import InitECandidate.Solver.MutableTable.WitnessDatabaseBefore

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The real workspace allocation and three stores retain a physical
immutable database and its frontier, when it precedes the current heap. -/
theorem ready_database (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes array table scratch : BitVec 64)
    (count maximum : Nat) (slices : Nat→Graph.Slice)
    (database : MutableTable.WitnessBuild.Database source array table count maximum slices scratch)
    (before : MutableTable.WitnessBuild.BeforeHeap source table heap.toNat) (arena : AllocatedBytes.Arena heap 40) :
    MutableTable.WitnessBuild.Database (ready source heap nodes root codes) array table count maximum slices scratch ∧
      MutableTable.WitnessBuild.BeforeHeap (ready source heap nodes root codes) table heap.toNat :=
  database.before_frame source (ready source heap nodes root codes) array table count maximum slices scratch heap.toNat before rfl rfl
    (fun query earlier=>ready_earlier source heap nodes root codes query arena earlier)

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.ready_database

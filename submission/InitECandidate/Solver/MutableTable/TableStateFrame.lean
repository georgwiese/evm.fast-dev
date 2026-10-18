import InitECandidate.Solver.MutableTable.TableState
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.MutableTable
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Preserve a live table across an actual write outside all of its pools. -/
theorem TableState.of_pool_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {kind : KeyHash.Kind} {plan : Plan} {slots : List Nat} {cursor floor : Nat}
    (table : TableState source kind plan slots cursor floor)
    (globals : target.globals = source.globals) (domain : target.memaddrs = source.memaddrs)
    (endian : target.be = source.be) (frame : MemoryModel.PoolFrame source.memory target.memory kind plan) :
    TableState target kind plan slots cursor floor := by
  refine ⟨table.valid, table.half, MemoryModel.Header.of_pool_frame _ _ _ _ _ table.header frame,
    MemoryModel.Occupied.of_pool_frame source target kind plan table.valid slots table.occupied domain endian frame,
    table.power, ?_, table.bounded, table.aligned, table.earlier, table.lower⟩
  rw [globals]
  exact table.heap

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.TableState.of_pool_frame

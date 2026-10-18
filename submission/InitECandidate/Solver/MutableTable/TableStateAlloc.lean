import InitECandidate.Solver.MutableTable.TableState
import InitECandidate.Solver.WitnessRadix.TableLocals

namespace InitECandidate.Solver.MutableTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- An actual allocator's canonical post-state advances a live table's
cursor invariant while preserving every existing table pool and word. -/
theorem TableState.after_alloc {source : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {plan : Plan} {slots : List Nat} {cursor floor : Nat}
    (table : TableState source kind plan slots cursor floor) (name : String) (next : Nat)
    (forward : cursor ≤ next) (bounded : next ≤ 33806089496) (aligned : next % 8 = 0) :
    TableState (PersistentAlloc.nextState source name cursor next) kind plan slots next floor := by
  refine ⟨table.valid, table.half, table.header, ?_, table.power, TableNew.allocated_heap source name cursor next, bounded, aligned, ?_, table.lower⟩
  · exact MemoryModel.Occupied.of_fields source (PersistentAlloc.nextState source name cursor next) kind plan slots table.occupied rfl rfl rfl
  · intro pool
    have before := table.earlier pool
    omega

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.TableState.after_alloc

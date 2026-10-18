import InitECandidate.Solver.MutableTable.TableFamily

namespace InitECandidate.Solver.MutableTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Table ownership depends on the current heap binding, not on unrelated
control globals such as journal_n. -/
theorem TableState.of_current_heap {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind}
    {plan : Plan} {slots : List Nat} {cursor floor : Nat} (table : TableState source kind plan slots cursor floor)
    (heap : target.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr"))
    (memory : target.memory = source.memory) (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) :
    TableState target kind plan slots cursor floor := by
  exact ⟨table.valid, table.half, by rw [memory]; exact table.header,
    MemoryModel.Occupied.of_fields source target kind plan slots table.occupied memory.symm domain.symm endian.symm,
    table.power, heap.trans table.heap, table.bounded, table.aligned, table.earlier, table.lower⟩

theorem TableFamily.Model.of_control {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → TableFamily.Object}
    (family : TableFamily.Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr"))
    (memory : target.memory = source.memory) (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) :
    TableFamily.Model target cursor objects :=
  ⟨fun index => (family.tables index).of_current_heap heap memory domain endian, family.apart⟩

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.TableState.of_current_heap
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.of_control

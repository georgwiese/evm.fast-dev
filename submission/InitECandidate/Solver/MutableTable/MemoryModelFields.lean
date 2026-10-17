import InitECandidate.Solver.MutableTable.MemoryModel

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact

/-- Physical table representation depends only on actual memory, mapping
and byte order. Caller locals, clocks, heap cursors and FFI bookkeeping do
not enter occupied/order/position reads. -/
theorem Occupied.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : NaturalLayout.Plan)
    (slots : List Nat) (occupied : Occupied source kind plan slots)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be) :
    Occupied target kind plan slots := by
  refine ⟨occupied.distinct, occupied.inside, ?_, ?_, ?_⟩
  · intro slot inside
    rw [← Find.usedByte_of_fields source target (NaturalLayout.parameters kind plan 0#64) _ memory domain endian]
    exact occupied.used slot inside
  · intro index
    rw [← memory]
    exact occupied.order index
  · intro index
    rw [← memory]
    exact occupied.position index

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Occupied.of_fields

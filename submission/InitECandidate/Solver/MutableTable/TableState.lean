import InitECandidate.Solver.MutableTable.MemoryModelFields

namespace InitECandidate.Solver.MutableTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Physical persistent-table invariant shared by actual original callers.
The lifetime floor protects earlier objects across every future growth. -/
structure TableState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat) : Prop where
  valid : Valid kind plan
  half : 2 * slots.length ≤ plan.capacity
  header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)
  occupied : MemoryModel.Occupied source kind plan slots
  power : ∃ bits, plan.capacity = 2 ^ bits ∧ 2 ≤ bits
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))
  bounded : cursor ≤ 33806089496
  aligned : cursor % 8 = 0
  earlier : ∀ pool, plan.base pool + size kind plan pool ≤ cursor
  lower : ∀ pool, floor ≤ plan.base pool

theorem TableState.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {plan : Plan} {slots : List Nat} {cursor floor : Nat}
    (table : TableState source kind plan slots cursor floor) (globals : target.globals = source.globals) (memory : target.memory = source.memory)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) : TableState target kind plan slots cursor floor := by
  refine ⟨table.valid, table.half, ?_, ?_, table.power, ?_, table.bounded, table.aligned, table.earlier, table.lower⟩
  · rw [memory]; exact table.header
  · exact MemoryModel.Occupied.of_fields source target kind plan slots table.occupied memory.symm domain.symm endian.symm
  · rw [globals]; exact table.heap

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.TableState.of_fields

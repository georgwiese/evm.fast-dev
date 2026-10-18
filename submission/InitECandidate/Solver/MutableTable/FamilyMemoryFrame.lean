import InitECandidate.Solver.MutableTable.FamilyControl
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- An unrelated allocation advances the common cursor while preserving all
owned pools. The actual new heap word and its range are explicit. -/
theorem Model.advance_cursor {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor nextCursor : Nat} {objects : ι → Object} (family : Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 nextCursor))))
    (forward : cursor ≤ nextCursor) (bounded : nextCursor ≤ 33806089496) (aligned : nextCursor % 8 = 0)
    (memory : target.memory = source.memory) (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) :
    Model target nextCursor objects := by
  refine ⟨?_, family.apart⟩
  intro index
  have table := family.tables index
  exact ⟨table.valid, table.half, by rw [memory]; exact table.header,
    MemoryModel.Occupied.of_fields source target _ _ _ table.occupied memory.symm domain.symm endian.symm,
    table.power, heap, bounded, aligned, (by intro pool; have before := table.earlier pool; omega), table.lower⟩

/-- A writer outside every live pool retains the complete table family. -/
theorem Model.of_pools {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor : Nat} {objects : ι → Object} (family : Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr"))
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (pools : ∀ index, MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan) :
    Model target cursor objects := by
  refine ⟨?_, family.apart⟩
  intro index
  have table := family.tables index
  exact ⟨table.valid, table.half, MemoryModel.Header.of_pool_frame source.memory target.memory _ _ _ table.header (pools index),
    MemoryModel.Occupied.of_pool_frame source target _ _ table.valid _ table.occupied domain endian (pools index),
    table.power, heap.trans table.heap, table.bounded, table.aligned, table.earlier, table.lower⟩

/-- Fresh allocations/copies beyond an earlier cursor retain every table,
even when the shared current heap cursor has already advanced. -/
theorem Model.of_earlier_words {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor cut : Nat} {objects : ι → Object} (family : Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr"))
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (earlier : ∀ index pool, (objects index).plan.base pool + size (objects index).kind (objects index).plan pool ≤ cut)
    (words : ∀ address : BitVec 64, address.toNat < cut → target.memory address = source.memory address) :
    Model target cursor objects := by
  apply family.of_pools heap domain endian
  intro index pool offset inside
  apply words
  rw [number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
  have before := earlier index pool
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.of_pools
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.of_earlier_words
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.advance_cursor

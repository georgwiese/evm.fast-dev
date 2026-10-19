import InitECandidate.Solver.MutableTable.FamilyMemoryFrame

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact NaturalLayout
open Flapjack.Basis.Pure.MlString

theorem Model.of_range {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff cursor : Nat} {objects : ι → Object} (family : Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr"))
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (floors : ∀ index, cutoff ≤ (objects index).floor)
    (words : ∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → target.memory query = source.memory query) :
    Model target cursor objects := by
  apply family.of_pools heap domain endian
  intro index pool offset inside
  have table := family.tables index
  have number := NaturalLayout.number (objects index).kind (objects index).plan table.valid pool offset inside
  apply words
  · rw [number]
    have lower := table.lower pool
    have floor := floors index
    omega
  · rw [number]
    have before := table.earlier pool
    omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.of_range

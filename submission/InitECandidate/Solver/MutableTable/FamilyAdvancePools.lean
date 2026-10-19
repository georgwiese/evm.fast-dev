import InitECandidate.Solver.MutableTable.FamilyMemoryFrame

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Unrelated allocation and writes outside owned pools advance the shared
cursor while retaining every table's actual physical representation. -/
theorem Model.advance_pools {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cursor nextCursor : Nat} {objects : ι → Object} (family : Model source cursor objects)
    (heap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 nextCursor))))
    (forward : cursor≤nextCursor) (bounded : nextCursor≤33806089496) (aligned : nextCursor%8=0)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan) :
    Model target nextCursor objects := by
  refine ⟨?_,family.apart⟩
  intro index
  have table := family.tables index
  exact ⟨table.valid,table.half,MemoryModel.Header.of_pool_frame source.memory target.memory _ _ _ table.header (pools index),
    MemoryModel.Occupied.of_pool_frame source target _ _ table.valid _ table.occupied domain endian (pools index),
    table.power,heap,bounded,aligned,(by intro pool; have before := table.earlier pool; omega),table.lower⟩

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.advance_pools

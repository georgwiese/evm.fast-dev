import InitECandidate.Solver.MutableTable.GrowRuntime.Prepared
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem reset_footprint (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) :
    TableFootprint.Frame memory (resetMemory memory plan) kind plan := by
  intro address outside
  have storesAway : address ∉ (resetWrites plan).map Prod.fst := by
    rw [reset_cells]
    intro member
    obtain ⟨offset, belongs, equal⟩ := List.mem_map.mp member
    exact outside .header offset (reset_site_bound offset belongs) equal.symm
  rw [resetMemory, WordWrites.write_away _ _ _ storesAway]
  apply Zero.final_memory_away
  intro offset inside
  change address ≠ cell plan .used 0 + BitVec.ofNat 64 offset
  rw [constant_cell]
  exact outside .used offset (used_offset_inside kind plan offset inside)

theorem prepared_footprint (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count : Nat) :
    TableFootprint.Frame source.memory (preparedState source kind old start count).memory kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  exact reset_footprint source.memory kind _

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_footprint
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_footprint

import InitECandidate.Solver.MutableTable.DeletePendingValues
import InitECandidate.Solver.MutableTable.DeleteFinishMemory

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The final occupancy clear and ordinal swap retain the actual values
of every surviving entry, independently of unused/stale words. -/
theorem PendingValues.finished (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole)
    (property : BitVec 64 → Prop) (values : PendingValues source plan deleted entries property) :
    Get.OccupiedValuesHave {source with memory:=Finish.memory source.memory plan deleted entries hole}
      (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) (finalSlots entries deleted) property := by
  intro slot inside member value stored
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (capacity_small kind plan valid)] at inside
  obtain ⟨ordinal,active,selected⟩ := (final_member entries deleted slot.toNat).mp member
  have extent : 8*slot.toNat<size kind plan .values := by change 8*slot.toNat<8*plan.capacity; omega
  rw [scaled_cell,Nat.mul_comm slot.toNat 8] at stored
  change Finish.memory source.memory plan deleted entries hole (cell plan .values (8*slot.toNat))=.word value at stored
  rw [Finish.memory,Finish.writes_pool_away _ kind plan valid count deleted entries pending.room pending.inside .values (by decide) (by decide) (by decide) _ extent,
    Finish.cleared_pool_away _ kind plan valid hole pending.holeInside .values (by decide) _ extent] at stored
  apply values ordinal active value
  rw [selected]
  exact stored

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.PendingValues.finished

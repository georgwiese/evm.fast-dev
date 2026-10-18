import InitECandidate.Solver.MutableTable.DeleteMoveMemory
import InitECandidate.Solver.MutableTable.DeleteInitial

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Complete physical hole/order invariant after the original movable
branch's copy and stores. Its hash-dependent choice is arbitrary; this proves
both the exchange and untouched used/header behavior without key assumptions. -/
theorem Pending.after_move (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted) (value : BitVec 64) :
    Pending {source with memory := Move.memory source.memory source.be kind plan hole (entries moved) moved.val value}
      kind plan count deleted (Function.update entries moved hole) (entries moved) := by
  classical
  have ordinalInside : moved.val < plan.capacity := Nat.lt_trans moved.isLt pending.room
  have movedInside := pending.inside moved active
  have different : hole ≠ entries moved := (pending.fresh moved).symm
  refine ⟨pending.room, entries_update_injective entries pending.distinct moved hole pending.fresh, ?_, ?_, movedInside,
    entries_update_fresh entries pending.distinct moved hole (entries moved) rfl different, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.update_of_ne (Ne.symm active)] using pending.sentinel
  · intro index notDeleted
    by_cases same : index = moved
    · subst index
      simpa only [Function.update_self] using pending.holeInside
    · simpa only [Function.update_of_ne same] using pending.inside index notDeleted
  · intro slot inside
    rw [Move.used_byte source kind plan valid hole (entries moved) moved.val value pending.holeInside ordinalInside slot inside]
    exact pending.binary slot inside
  · intro slot inside
    rw [Move.used_byte source kind plan valid hole (entries moved) moved.val value pending.holeInside ordinalInside slot inside, pending.used slot inside]
    exact (covered_update entries deleted moved hole (entries moved) slot active rfl).symm
  · intro index notDeleted
    have indexInside : index.val < plan.capacity := Nat.lt_trans index.isLt pending.room
    change Move.memory source.memory source.be kind plan hole (entries moved) moved.val value (cell plan .order (8 * index.val)) = _
    rw [Move.order_cell source.memory source.be kind plan valid hole (entries moved) moved.val value pending.holeInside ordinalInside index.val indexInside]
    by_cases same : index = moved
    · subst index
      simp only [Function.update_self, ↓reduceIte]
    · have different : index.val ≠ moved.val := fun equal => same (Fin.ext equal)
      rw [if_neg different]
      simpa only [Function.update_of_ne same] using pending.order index notDeleted
  · intro index notDeleted
    by_cases same : index = moved
    · subst index
      simp only [Function.update_self]
      change Move.memory source.memory source.be kind plan hole (entries moved) moved.val value (cell plan .position (8 * hole)) = _
      rw [Move.position_cell source.memory source.be kind plan valid hole (entries moved) moved.val value pending.holeInside ordinalInside hole pending.holeInside, if_pos rfl]
    · simp only [Function.update_of_ne same]
      change Move.memory source.memory source.be kind plan hole (entries moved) moved.val value (cell plan .position (8 * entries index)) = _
      rw [Move.position_cell source.memory source.be kind plan valid hole (entries moved) moved.val value pending.holeInside ordinalInside (entries index) (pending.inside index notDeleted), if_neg (pending.fresh index)]
      exact pending.position index notDeleted

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.Pending.after_move

import InitECandidate.Solver.MutableTable.DeleteFinishArrays

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Clearing the moving hole, applying the original last-entry swap and
storing count-1 establishes the full physical occupied/order/position model
for exactly the surviving ordinals. Runtime execution is proved separately. -/
theorem occupied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) :
    MemoryModel.Occupied {source with memory := memory source.memory plan deleted entries hole} kind plan (finalSlots entries deleted) := by
  classical
  constructor
  · exact final_distinct entries deleted pending.distinct
  · intro slot member
    obtain ⟨index, active, same⟩ := (final_member entries deleted slot).mp member
    rw [← same]
    exact pending.inside index active
  · intro slot inside
    rw [used_byte source kind plan valid domain little count deleted entries hole pending slot inside]
    by_cases atHole : slot = hole
    · have missing : slot ∉ finalSlots entries deleted := by
        intro member
        obtain ⟨index, active, same⟩ := (final_member entries deleted slot).mp member
        exact pending.fresh index (same.trans atHole)
      rw [if_pos atHole, if_neg missing]
    · have oneIff : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some 1 ↔ slot ∈ finalSlots entries deleted := by
        rw [pending.used slot inside, final_member entries deleted slot]
        constructor
        · rintro (same | member)
          · exact (atHole same).elim
          · exact member
        · intro member; exact Or.inr member
      rw [if_neg atHole]
      by_cases member : slot ∈ finalSlots entries deleted
      · rw [if_pos member]
        exact oneIff.mpr member
      · rw [if_neg member]
        rcases pending.binary slot inside with zero | one
        · exact zero
        · exact (member (oneIff.mp one)).elim
  · intro index
    let ordinal : Fin (count - 1) := ⟨index.val, by simpa only [final_length] using index.isLt⟩
    have selected : (finalSlots entries deleted).get index = entries (remainingOrdinal deleted ordinal) := by
      exact final_get entries deleted ordinal
    rw [selected]
    exact final_order source kind plan valid count deleted entries hole pending ordinal
  · intro index
    let ordinal : Fin (count - 1) := ⟨index.val, by simpa only [final_length] using index.isLt⟩
    have selected : (finalSlots entries deleted).get index = entries (remainingOrdinal deleted ordinal) := by
      exact final_get entries deleted ordinal
    rw [selected]
    exact final_position source kind plan valid count deleted entries hole pending ordinal

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.occupied

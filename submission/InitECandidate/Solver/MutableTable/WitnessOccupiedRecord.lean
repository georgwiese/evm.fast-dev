import InitECandidate.Solver.MutableTable.WitnessLookupAnyOrigin

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
attribute [local instance] Classical.propDecidable

/-- Any physically selected occupied record is an actual last-write value
of the genuine constructor history. The query's key is not used. -/
theorem occupied_record_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits) (scratch : BitVec 64) (count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical) (query record : BitVec 64)
    (selected : OccupiedRecord source plan query record) : ∃ key,lastValue key input=some record := by
  obtain ⟨slot,inside,⟨byte,nonzero,loaded⟩,stored⟩ := selected
  have capSmall : plan.capacity<2^64 := by rw [power]; exact Nat.pow_lt_pow_right (by decide) small
  have capNumber : (Layout32.parameters plan query).capacity.toNat=plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat=plan.capacity
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  have slotInside : slot.toNat<plan.capacity := by rwa [capNumber] at inside
  have used:=built.keys.used slot.toNat slotInside
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at used
  have sameUsed : Find.usedByte source (Layout32.parameters plan scratch) slot=Find.usedByte source (Layout32.parameters plan query) slot := rfl
  rw [sameUsed] at used
  cases cell : logical slot.toNat with
  | none =>
    rw [cell] at used
    exact (nonzero (Option.some.inj (loaded.symm.trans used))).elim
  | some entry =>
    obtain ⟨key,value⟩ := entry
    have payload:=built.values slot.toNat slotInside key value cell
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at payload
    have valueEq : record=value := HolWordLab.word.inj (stored.symm.trans payload.2)
    have invariants:=Placement.build_invariants plan.capacity (Find.hashHome bits) input logical built.trace
    have found:=invariants.2.1.1 slot.toNat slotInside key value cell
    exact ⟨key,by rw [valueEq]; exact found⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.occupied_record_key

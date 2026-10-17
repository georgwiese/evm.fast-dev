import InitECandidate.Solver.GasBudget.StateCharge

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack PanSemStateFiniteExact

theorem preserves_regular_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill) (affordable : amount.toNat≤state.toNat+gas.toNat)
    (fits : gas.toNat+spill.toNat<2^64) :
    regularBudget (WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount)) frame=regularBudget source.memory frame := by
  by_cases reservoir : amount≤state
  · have unchanged : ∀ offset∈([64,184,192] : List Nat),
        WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount) (frame+BitVec.ofNat 64 offset)=source.memory (frame+BitVec.ofNat 64 offset) := by
      intro offset member
      apply WitnessRadix.WordWrites.write_away
      rw [poolWrites,if_pos reservoir]
      have offsetNe : BitVec.ofNat 64 offset≠72#64 := by
        have choices : offset=64 ∨ offset=184 ∨ offset=192 := by simpa using member
        rcases choices with rfl|rfl|rfl <;> decide
      simp [offsets_ne frame _ _ offsetNe]
    simp only [regularBudget,wordAt,unchanged 64 (by simp),unchanged 184 (by simp),unchanged 192 (by simp)]
  · have stateLe : state≤amount := by change ¬amount.toNat≤state.toNat at reservoir; change state.toNat≤amount.toNat; omega
    have remainderNat : (amount-state).toNat=amount.toNat-state.toNat:=BitVec.toNat_sub_of_le stateLe
    have remainderBound : amount-state≤gas := by change (amount-state).toNat≤gas.toNat; rw [remainderNat]; omega
    have d7264:=offsets_ne frame 72#64 64#64 (by decide)
    have d72192:=offsets_ne frame 72#64 192#64 (by decide)
    have d64192:=offsets_ne frame 64#64 192#64 (by decide)
    have distinct : ((poolWrites frame gas state spill amount).map Prod.fst).Nodup := by
      simp [poolWrites,if_neg reservoir,d7264,d72192,d64192]
    have gasAfter:=WitnessRadix.WordWrites.write_unique source.memory (poolWrites frame gas state spill amount) (frame+64#64,gas-(amount-state)) distinct
      (by simp [poolWrites,if_neg reservoir])
    have spillAfter:=WitnessRadix.WordWrites.write_unique source.memory (poolWrites frame gas state spill amount) (frame+192#64,spill+(amount-state)) distinct
      (by simp [poolWrites,if_neg reservoir])
    have usedAfter:=WitnessRadix.WordWrites.write_away source.memory (poolWrites frame gas state spill amount) (frame+184#64)
      (by simp [poolWrites,if_neg reservoir,offsets_ne frame 184#64 72#64 (by decide),offsets_ne frame 184#64 64#64 (by decide),offsets_ne frame 184#64 192#64 (by decide)])
    have gasSmall : (amount-state).toNat≤gas.toNat:=remainderBound
    simp only [regularBudget,wordAt,gasAfter,spillAfter,usedAfter,pools.gas,pools.spill,WitnessRadix.MemoryBytes.wordBits]
    change (gas-(amount-state)).toNat+(wordAt source.memory (frame+184#64)).toNat+(spill+(amount-state)).toNat=
      gas.toNat+(wordAt source.memory (frame+184#64)).toNat+spill.toNat
    rw [BitVec.toNat_sub_of_le remainderBound,BitVec.toNat_add_of_lt (by omega)]
    omega

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.preserves_regular_budget

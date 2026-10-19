import InitECandidate.Solver.GasBudget.MemoryExpansionCostValue
import InitECandidate.Solver.GasBudget.MemoryGasArithmetic

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Input.RlpWrite

/-- Arithmetic consequences for the length to be stored by extend_memory.
The actual expansion writes and loop executions are separate obligations. -/
structure Advance (current expand amount : BitVec 64) (used : Nat) : Prop where
  natural : (current + expand).toNat = current.toNat + expand.toNat
  covered : (MemoryGasCost.resultWord (current + expand)).toNat ≤ used + amount.toNat
  aligned : (current + expand).toNat % 32 = 0
  byteBound : (current + expand).toNat ≤ 178956960

theorem zero_advance (current amount : BitVec 64) (used gas : Nat) (aligned : current.toNat % 32 = 0)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ used) (pool : used + gas ≤ 16777216) :
    Advance current 0#64 amount used := by
  have bytes := MemoryGasCost.byte_bound current (by omega)
  constructor
  · simp
  · simp only [BitVec.add_zero]
    omega
  · simpa using aligned
  · simp only [BitVec.add_zero]
    omega

theorem end_advance (current endp amount : BitVec 64) (used gas : Nat) (aligned : current.toNat % 32 = 0)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ used) (pool : used + gas ≤ 16777216)
    (affordable : amount.toNat ≤ gas) (covers : (endPair current endp).1.toNat ≤ amount.toNat) :
    Advance current (endPair current endp).2 amount used := by
  by_cases endpointMax : endp = 18446744073709551615#64
  · rw [endPair, if_pos endpointMax] at covers
    change 18446744073709551615 ≤ amount.toNat at covers
    omega
  · rw [endPair, if_neg endpointMax, Ceil32.fixed_of_aligned current aligned] at covers ⊢
    let next := Ceil32.resultWord endp
    by_cases noGrowth : next ≤ current
    · rw [if_pos noGrowth]
      exact zero_advance current amount used gas aligned covered pool
    · rw [if_neg noGrowth] at covers ⊢
      by_cases costMax : MemoryGasCost.resultWord next = 18446744073709551615#64
      · rw [finalPair, if_pos costMax] at covers
        change 18446744073709551615 ≤ amount.toNat at covers
        omega
      · rw [finalPair, if_neg costMax] at covers ⊢
        change (MemoryGasCost.resultWord next - MemoryGasCost.resultWord current).toNat ≤ amount.toNat at covers
        obtain ⟨nextCovered, costOrder, deltaExact⟩ := MemoryGasCost.charge_covers (MemoryGasCost.resultWord current)
          (MemoryGasCost.resultWord next) amount used gas covered pool affordable covers
        have nextSmall : (MemoryGasCost.resultWord next).toNat ≤ 16777216 := by omega
        have bytes := MemoryGasCost.byte_bound next nextSmall
        have notMax : next ≠ 18446744073709551615#64 := by
          intro equal
          have number := congrArg BitVec.toNat equal
          change next.toNat = 18446744073709551615 at number
          omega
        have nextAligned : next.toNat % 32 = 0 := Ceil32.aligned_of_not_max endp notMax
        have order : current ≤ next := by change ¬next.toNat ≤ current.toNat at noGrowth; change current.toNat ≤ next.toNat; omega
        have naturalDelta := BitVec.toNat_sub_of_le order
        have wordEq : current + (next - current) = next := by rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
        constructor
        · rw [wordEq, naturalDelta]
          change current.toNat ≤ next.toNat at order
          omega
        · rw [wordEq]
          exact nextCovered
        · rw [wordEq]
          exact nextAligned
        · rw [wordEq]
          omega

theorem affordable (start size : U256Value.Words) (current amount : BitVec 64) (used gas : Nat)
    (aligned : current.toNat % 32 = 0) (covered : (MemoryGasCost.resultWord current).toNat ≤ used)
    (pool : used + gas ≤ 16777216) (funded : amount.toNat ≤ gas)
    (covers : (resultPair start size current).1.toNat ≤ amount.toNat) :
    Advance current (resultPair start size current).2 amount used := by
  by_cases zero : U256Zero.resultWord size ≠ 0#64
  · rw [resultPair, if_pos zero]
    exact zero_advance current amount used gas aligned covered pool
  · rw [resultPair, if_neg zero] at covers ⊢
    exact end_advance current _ amount used gas aligned covered pool funded covers

theorem pair_value_injective : Function.Injective pairValue := by
  rintro ⟨left, right⟩ ⟨otherLeft, otherRight⟩ equal
  simpa [pairValue] using equal

/-- Actual normal original helper plus an actual affordable covering charge
derives the next-length alignment, no-wrap and cost potential. This is still
a local transition, not a reachable whole-run budget or target bound. -/
theorem normal_affordable (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (start size : U256Value.Words) (view : View source frame current)
    (startLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "size") = some (U256Value.tuple size))
    (delta expand amount : BitVec 64) (used gas : Nat)
    (aligned : current.toNat % 32 = 0) (covered : (MemoryGasCost.resultWord current).toNat ≤ used)
    (pool : used + gas ≤ 16777216) (funded : amount.toNat ≤ gas) (covers : delta.toNat ≤ amount.toNat)
    (normal : evaluateHOLFiniteState source body = (some (.returned (pairValue (delta, expand))), post)) :
    Advance current expand amount used := by
  have values := pair_value_injective (normal_value source post frame current start size view startLocal sizeLocal _ normal)
  have first := congrArg Prod.fst values
  have second := congrArg Prod.snd values
  change delta = (resultPair start size current).1 at first
  change expand = (resultPair start size current).2 at second
  rw [first] at covers
  rw [second]
  exact affordable start size current amount used gas aligned covered pool funded covers

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.affordable
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.normal_affordable

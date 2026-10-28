import InitECandidate.Solver.Input.CounterFlow
import InitECandidate.Solver.Input.LocalFlow
import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

def counterWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS) : BitVec 64 :=
  valueWord ((source.locals.lookup key).getD (.val (.word 0#64)))

/-- Actual unsigned local-counter loops: preserve their real limit, advance
one word without wrapping, and charge the actual bounded body at each tick.
All outcomes are covered; no completed loop trace is a premise. -/
theorem loop_snapshot_cost (code) (counter limit : MlS) (snapshot : Option (ValueHOL 64)) (test : ExpHOL 64) (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^64)
    (testReads : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory, ∀ current : BitVec 64,
      state.locals.lookup counter = some (.val (.word current)) →
      state.locals.lookup limit = snapshot → current.toNat ≤ length →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) test =
        some (.val (.word (if current.toNat < length then 1#64 else 0#64))))
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalFlow limit body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup limit = snapshot)
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  classical
  let invariant := fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    ∃ current : BitVec 64, state.locals.lookup counter = some (.val (.word current)) ∧
      state.locals.lookup limit = snapshot ∧ current.toNat ≤ length
  let rank := fun state : PanSemStateFiniteExact 64 Guest.HostMemory => length - (counterWord state counter).toNat
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,
      state.code = code → invariant state → ∀ observed : BitVec 64,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        test = some (.val (.word observed)) →
      observed ≠ 0 → 0 < rank state ∧
        (state.clock ≠ 0 → let output := evaluateHOLFiniteState (decClockHOLFinite state) body
          (output.1 = none ∨ output.1 = some .continue) → invariant output.2 ∧ rank output.2 < rank state) := by
    intro state codeEq valid observed actual nonzero
    obtain ⟨current, currentCell, lengthCell, bounded⟩ := valid
    have read := testReads state current currentCell lengthCell bounded
    have active : current.toNat < length := by
      by_cases active : current.toNat < length
      · exact active
      · rw [if_neg active] at read
        have equal : observed = 0#64 := by
          simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using actual.symm.trans read
        exact (nonzero equal).elim
    have rankEq : rank state = length - current.toNat := by simp [rank, counterWord, currentCell, valueWord]
    refine ⟨by rw [rankEq]; omega, ?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    have summary := safe.summary (decClockHOLFinite state)
    unfold FlowSummary at summary
    have normal : output.1 = none := by
      rcases continuing with normal | continued
      · exact normal
      · exact (summary.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite state) body = (none, output.2) := Prod.ext normal rfl
    have nextCell := advance (decClockHOLFinite state) output.2 current currentCell run
    have nextLimit := (summary.1 normal).trans lengthCell
    have nextNumber : (current + 1#64).toNat = current.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change current.toNat + 1 < 2^64; omega)]
      rfl
    have nextRank : rank output.2 = length - (current.toNat + 1) := by
      simp only [rank, counterWord, nextCell, Option.getD_some, valueWord, nextNumber]
    refine ⟨⟨current + 1#64, nextCell, nextLimit, by rw [nextNumber]; omega⟩, ?_⟩
    rw [nextRank, rankEq]
    omega
  have bounded := ClockCost.ranked_loop code _ body price invariant rank priced progress source installed
    ⟨word, counterCell, limitCell, initial⟩
  simpa only [rank, counterWord, counterCell, Option.getD_some, valueWord] using bounded

/-- Compatibility interface for a preserved scalar limit and no early return. -/
theorem loop_cost_test (code) (counter limit : MlS) (test : ExpHOL 64) (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^64)
    (testReads : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory, ∀ current : BitVec 64,
      state.locals.lookup counter = some (.val (.word current)) →
      state.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))) → current.toNat ≤ length →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) test =
        some (.val (.word (if current.toNat < length then 1#64 else 0#64))))
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalPrefix limit body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  exact loop_snapshot_cost code counter limit (some (.val (.word (BitVec.ofNat 64 length))))
    test body price length lengthBound testReads priced advance (.base safe)
    source word installed counterCell limitCell initial

/-- Unsigned counter comparison, sharing the same checked rank proof. -/
theorem loop_cost (code) (counter limit : MlS) (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^64)
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalPrefix limit body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while (.cmp .lower (.var .local counter) (.var .local limit)) body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  apply loop_cost_test code counter limit (.cmp .lower (.var .local counter) (.var .local limit)) body price length lengthBound
  · intro state current currentCell lengthCell bounded
    have lengthMod : length % 18446744073709551616 = length := Nat.mod_eq_of_lt lengthBound
    simp [evalHOLFinite, evalHOLExact, toExact, currentCell, lengthCell, wordCmpHOL, BitVec.lt_def,
      BitVec.toNat_ofNat, lengthMod]
  · exact priced
  · exact advance
  · exact safe
  · exact installed
  · exact counterCell
  · exact limitCell
  · exact initial

/-- Signed comparison on the actual nonnegative, nonwrapping counter range. -/
theorem signed_loop_cost (code) (counter limit : MlS) (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^63)
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalPrefix limit body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup limit = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while (.cmp .less (.var .local counter) (.var .local limit)) body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  apply loop_cost_test code counter limit (.cmp .less (.var .local counter) (.var .local limit)) body price length (by omega)
  · intro state current currentCell lengthCell bounded
    have lengthNumber : (BitVec.ofNat 64 length).toNat = length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have currentSmall : current.toNat < 9223372036854775808 := by omega
    have lengthSmall : length < 9223372036854775808 := lengthBound
    simp [evalHOLFinite, evalHOLExact, toExact, currentCell, lengthCell, wordCmpHOL,
      holAsmSignedLess, lengthNumber, currentSmall, lengthSmall]
  · exact priced
  · exact advance
  · exact safe
  · exact installed
  · exact counterCell
  · exact limitCell
  · exact initial

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.loop_cost

#print axioms InitECandidate.Solver.Input.CounterFlow.loop_cost_test
#print axioms InitECandidate.Solver.Input.CounterFlow.signed_loop_cost

#print axioms InitECandidate.Solver.Input.CounterFlow.loop_snapshot_cost

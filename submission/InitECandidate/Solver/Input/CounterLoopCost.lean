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

namespace InitECandidate.Solver.Input.GeometricLoop

/-- A positive natural term doubled by each real continuing step reaches
the word limit after at most its bit width many such steps. -/
theorem doubling_lower (values : Nat→Nat) (steps : Nat) (positive : 0<values 0)
    (grows : ∀ index<steps,2*values index≤values (index+1)) : 2^steps≤values steps := by
  induction steps with
  | zero=>simpa using (show 1≤values 0 from by omega)
  | succ steps ih=>
    have previous:=ih (by intro index inside; exact grows index (by omega))
    calc
      2^(steps+1)=2*2^steps:=by rw [Nat.pow_succ,Nat.mul_comm]
      _≤2*values steps:=Nat.mul_le_mul_left 2 previous
      _≤values (steps+1):=grows steps (by omega)

theorem doubling_exceeds_word (values : Nat→Nat) (bits : Nat) (positive : 0<values 0)
    (grows : ∀ index<bits,2*values index≤values (index+1)) (bounded : values bits<2^bits) : False :=
  Nat.not_le_of_lt bounded (doubling_lower values bits positive grows)

/-- Repeated halving consumes a finite unsigned word in at most its bit
width many actual continuing steps, including truncating integer division. -/
theorem halving_weighted (values : Nat→Nat) (steps : Nat)
    (shrinks : ∀ index<steps,2*values (index+1)≤values index) : 2^steps*values steps≤values 0 := by
  induction steps with
  | zero=>simp
  | succ steps ih=>
    have previous:=ih (by intro index inside; exact shrinks index (by omega))
    calc
      2^(steps+1)*values (steps+1)=2^steps*(2*values (steps+1)):=by rw [Nat.pow_succ,Nat.mul_assoc]
      _≤2^steps*values steps:=Nat.mul_le_mul_left _ (shrinks steps (by omega))
      _≤values 0:=previous

theorem halving_zero (values : Nat→Nat) (bits : Nat) (bounded : values 0<2^bits)
    (shrinks : ∀ index<bits,2*values (index+1)≤values index) : values bits=0 := by
  have weighted:=halving_weighted values bits shrinks
  by_cases zero : values bits=0
  · exact zero
  · have positive : 1≤values bits:=by omega
    have power : 2^bits≤2^bits*values bits:=by simpa using Nat.mul_le_mul_left (2^bits) positive
    omega

theorem quotient_double (accumulator numerator divisor : Nat) (positive : 0<divisor) (large : 2*divisor≤numerator) :
    2*accumulator≤accumulator*numerator/divisor := by
  apply (Nat.le_div_iff_mul_le positive).mpr
  calc
    (2*accumulator)*divisor=accumulator*(2*divisor):=by ac_rfl
    _≤accumulator*numerator:=Nat.mul_le_mul_left accumulator large

theorem quotient_half (accumulator numerator divisor : Nat) (small : 2*numerator≤divisor) :
    2*(accumulator*numerator/divisor)≤accumulator := by
  by_cases zero : numerator=0
  · simp [zero]
  · have paid : (2*(accumulator*numerator/divisor))*numerator≤accumulator*numerator:=by
      calc
        (2*(accumulator*numerator/divisor))*numerator=(accumulator*numerator/divisor)*(2*numerator):=by ac_rfl
        _≤(accumulator*numerator/divisor)*divisor:=Nat.mul_le_mul_left _ small
        _≤accumulator*numerator:=Nat.div_mul_le_self _ _
    apply Nat.le_of_not_gt
    intro smaller
    have strict:=Nat.mul_lt_mul_of_pos_right smaller (by omega : 0<numerator)
    omega

/-- Numerical branch used by the unchanged Taylor loop: before index257,
a numerator at least512denominator forces doubling of every normal term. -/
theorem taylor_large_step (accumulator numerator denominator index : Nat)
    (denominatorPositive : 0<denominator) (indexPositive : 0<index) (indexBound : index≤256)
    (large : 512*denominator≤numerator) :
    2*accumulator≤accumulator*numerator/(denominator*index) := by
  apply quotient_double accumulator numerator (denominator*index) (Nat.mul_pos denominatorPositive indexPositive)
  have bound:=Nat.mul_le_mul_left denominator indexBound
  omega

/-- In the other branch the actual Taylor term halves from index1024 on.
This is a natural recurrence fact; the real arithmetic-call bridge is separate. -/
theorem taylor_small_step (accumulator numerator denominator index : Nat)
    (indexBound : 1024≤index) (small : numerator<512*denominator) :
    2*(accumulator*numerator/(denominator*index))≤accumulator := by
  apply quotient_half
  have bound:=Nat.mul_le_mul_left denominator indexBound
  omega

end InitECandidate.Solver.Input.GeometricLoop

#print axioms InitECandidate.Solver.Input.GeometricLoop.doubling_lower
#print axioms InitECandidate.Solver.Input.GeometricLoop.doubling_exceeds_word
#print axioms InitECandidate.Solver.Input.GeometricLoop.halving_weighted
#print axioms InitECandidate.Solver.Input.GeometricLoop.halving_zero
#print axioms InitECandidate.Solver.Input.GeometricLoop.quotient_double
#print axioms InitECandidate.Solver.Input.GeometricLoop.quotient_half
#print axioms InitECandidate.Solver.Input.GeometricLoop.taylor_large_step
#print axioms InitECandidate.Solver.Input.GeometricLoop.taylor_small_step

namespace InitECandidate.Solver.Input.GeometricLoop

/-- Any positive finite-word Taylor prefix obeying the exact natural
recurrence has fewer than1280continuing steps. This does not assume an
infinite execution, a future successful arithmetic call or a loop result. -/
theorem taylor_positive_prefix (values : Nat→Nat) (numerator denominator steps : Nat)
    (denominatorPositive : 0<denominator)
    (terms : ∀ index≤steps,0<values index ∧ values index<2^256)
    (recurrence : ∀ index<steps,values (index+1)=values index*numerator/(denominator*(index+1))) : steps<1280 := by
  apply Nat.lt_of_not_ge
  intro long
  by_cases large : 512*denominator≤numerator
  · have grows : ∀ index<256,2*values index≤values (index+1):=by
      intro index inside
      rw [recurrence index (by omega)]
      exact taylor_large_step (values index) numerator denominator (index+1) denominatorPositive (by omega) (by omega) large
    exact doubling_exceeds_word values 256 (terms 0 (by omega)).1 grows (terms 256 (by omega)).2
  · have small : numerator<512*denominator:=by omega
    let shifted:=fun index=>values (1023+index)
    have shrinks : ∀ index<256,2*shifted (index+1)≤shifted index:=by
      intro index inside
      change 2*values (1023+(index+1))≤values (1023+index)
      have same : 1023+(index+1)=(1023+index)+1:=by omega
      rw [same,recurrence (1023+index) (by omega)]
      exact taylor_small_step (values (1023+index)) numerator denominator (1023+index+1) (by omega) small
    have zero:=halving_zero shifted 256 (terms 1023 (by omega)).2 shrinks
    have positive:= (terms 1279 (by omega)).1
    change values 1279=0 at zero
    omega

end InitECandidate.Solver.Input.GeometricLoop

#print axioms InitECandidate.Solver.Input.GeometricLoop.taylor_positive_prefix

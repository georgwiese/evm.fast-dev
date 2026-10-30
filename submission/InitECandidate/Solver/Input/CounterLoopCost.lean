import InitECandidate.Solver.Input.RlpWrite.U256Shape
import InitECandidate.Solver.Input.ClockCostCallReached
import InitECandidate.Solver.Input.TrapCost
import InitECandidate.Solver.Input.ClockCostCurrentGuard
import InitECandidate.Solver.Input.ContinuingDeclarationEntry
import InitECandidate.Solver.GasBudget.Mul64Value
import InitECandidate.Solver.Input.UDivMod.CurrentFrame
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostCurrentValue
import InitECandidate.Solver.Input.ClockCostDeclaredReached
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.CurrentVerify.GasFrame
import InitECandidate.Solver.Input.ClockCostCurrentLoop
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

namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Both existing scalar-word encodings denote the same actual quad. -/
theorem wordQuad_remainder (word : BitVec 64) : wordQuad word=Input.UDivMod.WideDigits.Single.remainderWords word := by
  funext index
  by_cases zero : index=0
  · subst index
    rfl
  · have nonzero : index.val≠0:=by intro same;exact zero (Fin.ext same)
    simp only [wordQuad,Input.UDivMod.WideDigits.Single.remainderWords,if_neg zero,if_neg nonzero]


end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.wordQuad_remainder

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def denominator (index : Nat) : BitVec 64:=BitVec.ofNat 64 (index*11684671)

theorem denominator_number (index : Nat) (bounded : index≤1280) :
    (denominator index).toNat=index*11684671 := by
  rw [denominator,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem denominator_bounds (index : Nat) (positive : 0<index) (bounded : index≤1280) :
    0<(denominator index).toNat ∧ (denominator index).toNat≤14956378880 ∧ (denominator index).toNat≤2^63 := by
  rw [denominator_number index bounded]
  omega

/-- The actual index/denominator multiplication is a single-word result
through the full existing u256_mul ABI at every potentially active index. -/
theorem denominator_product (index : Nat) (bounded : index≤1280) :
    GasBudget.U256Multiply.productQuad (BitVec.ofNat 64 index) 11684671#64=
      UDivMod.WideDigits.Single.remainderWords (denominator index) := by
  have encoded : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have constant : (11684671#64 : BitVec 64).toNat=11684671:=rfl
  rw [GasBudget.U256Multiply.productQuad_word _ _ (by rw [encoded,constant];omega),GasBudget.U256Multiply.wordQuad_remainder,encoded,constant]
  rfl

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.denominator_number
#print axioms InitECandidate.Solver.Input.TaylorCurrent.denominator_bounds
#print axioms InitECandidate.Solver.Input.TaylorCurrent.denominator_product

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev Quad:=RlpWrite.U256Value.Words

def body : ProgHOL 64:=match Guest.Software.guestFn_taylor_exponential with | .function fn=>progToHOL fn.body | _=>.skip

def increment : ExpHOL 64:=.op .add [localVar "i",.const 1#64]
def finishIteration : ProgHOL 64:=.seq (.assign .local (ofString "i") increment)
  (.call (some (some (.local,ofString "nz"),none)) (ofString "u256_is_zero") [localVar "acc"])
def afterDenominator : ProgHOL 64:=.seq
  (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_div") [localVar "p",localVar "di"]) finishIteration
def afterWord : ProgHOL 64:=.seq
  (.call (some (some (.local,ofString "di"),none)) (ofString "u256_mul") [localVar "di",localVar "den"]) afterDenominator
def divisionStep : ProgHOL 64:=.decCall (ofString "di") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "i"] afterWord

def overflowTest : ExpHOL 64:=.cmp .notEqual (.op .or [.rfield 4 (localVar "prod"),.rfield 5 (localVar "prod"),.rfield 6 (localVar "prod"),.rfield 7 (localVar "prod")]) (.const 0#64)
def overflowGuard : ProgHOL 64:=.ite overflowTest (.call (some (none,none)) (ofString "trap_with") [.const 3#64]) .skip

def lowProduct : ExpHOL 64:=.rstruct [.rfield 0 (localVar "prod"),.rfield 1 (localVar "prod"),.rfield 2 (localVar "prod"),.rfield 3 (localVar "prod")]
def afterProduct : ProgHOL 64:=.seq overflowGuard (.dec (ofString "p") RlpWrite.U256Value.tupleShape lowProduct divisionStep)
def iteration : ProgHOL 64:=.seq
  (.call (some (some (.local,ofString "out"),none)) (ofString "u256_add") [localVar "out",localVar "acc"])
  (.decCall (ofString "prod") (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) (ofString "u256_mul_full") [localVar "acc",localVar "num"] afterProduct)
def loopTest : ExpHOL 64:=.cmp .equal (localVar "nz") (.const 0#64)
def loop : ProgHOL 64:=.while loopTest iteration

def finalReturn : ProgHOL 64:=.seq
  (.call (some (some (.local,ofString "out"),none)) (ofString "u256_div") [localVar "out",localVar "den"])
  (.return (localVar "out"))
def afterZero : ProgHOL 64:=.seq loop finalReturn

def initial : ProgHOL 64:=
  .seq (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_mul") [localVar "acc",localVar "den"])
    (.dec (ofString "out") RlpWrite.U256Value.tupleShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
      (.dec (ofString "i") .one (.const 1#64)
        (.dec (ofString "zero") RlpWrite.U256Value.tupleShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
          (.decCall (ofString "nz") .one (ofString "u256_is_zero") [localVar "acc"] afterZero))))

/-- This is the literal current Taylor program, including its overflow
trap, arithmetic argument order, scopes, counter and both divisions. -/
theorem body_shape : body=
    .decCall (ofString "den") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "denominator"]
      (.decCall (ofString "num") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "numerator"]
        (.decCall (ofString "acc") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "factor"] initial)) := by
  simp [body,Guest.Software.guestFn_taylor_exponential,progToHOL,expToHOL,shapeToHOL,localVar,
    initial,afterZero,loop,loopTest,iteration,afterProduct,overflowGuard,overflowTest,lowProduct,
    divisionStep,afterWord,afterDenominator,finishIteration,increment,finalReturn,RlpWrite.U256Value.tupleShape]

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.body_shape

namespace InitECandidate.Solver.GasBudget.U256Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem assigned_call_cost (code) (installed : Input.OriginalCode.Installed code)
    (name : MlS) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (some (some (.local,name),none)) (ofString "u256_is_zero") arguments) 1 := by
  have price:=ArithmeticEffects.price_u256_is_zero code (ArithmeticEffects.current_environment code installed)
  exact Input.ClockCost.call_body code (some (some name)) (ofString "u256_is_zero") arguments formals body .one 0
    (current_code code installed) price

/-- The actual assigned zero-test derives its own call tick, exact flag
and read-only caller state from the same genuine normal execution. -/
theorem assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Quad)
    (installed : Input.OriginalCode.Installed source.code) (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [Input.RlpWrite.U256Value.tuple words])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "u256_is_zero") arguments)=(none,post)) :
    1≤source.clock ∧ post=setVarHOLFinite name (.val (.word (resultWord words))) {source with clock:=source.clock-1} := by
  obtain ⟨funded,values,actual,callee,shape,target,returned,actualArgs,called,childRun,typed,postEq⟩:=
    Input.CallNormal.local_data source post name (ofString "u256_is_zero") arguments normal
  have valuesEq : values=[Input.RlpWrite.U256Value.tuple words]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  obtain ⟨expected,lookup,aCell⟩:=Input.RlpWrite.U256Value.environment source.code.lookup (ofString "u256_is_zero") body words (current_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at aCell
  rw [bodyEq] at childRun
  have checked:=execute (callEntryStateHOLFinite source callee) words aCell
  have returnedEq : returned=.val (.word (resultWord words)):=by
    have value:=congrArg Prod.fst (childRun.symm.trans checked)
    cases value
    rfl
  have targetEq : target=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee):=congrArg Prod.snd (childRun.symm.trans checked)
  have frame : {target with locals:=source.locals}={source with clock:=source.clock-1}:=by
    rw [targetEq]
    rfl
  exact ⟨funded,by rw [postEq,returnedEq,frame]⟩

end InitECandidate.Solver.GasBudget.U256Zero

#print axioms InitECandidate.Solver.GasBudget.U256Zero.assigned_call_cost
#print axioms InitECandidate.Solver.GasBudget.U256Zero.assigned_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem finish_iteration_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code finishIteration 1 := by
  exact ClockCost.sequence code (.assign .local (ofString "i") increment)
    (.call (some (some (.local,ofString "nz"),none)) (ofString "u256_is_zero") [localVar "acc"]) 0 1
    (ClockCost.assign code _ _) (GasBudget.U256Zero.assigned_call_cost code installed _ _)

/-- A genuine completed iteration tail has the exact counter increment
and zero flag of the actual next accumulator, with one real call tick. -/
theorem finish_iteration_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (accumulator : Quad)
    (installed : OriginalCode.Installed source.code)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (normal : evaluateHOLFiniteState source finishIteration=(none,post)) :
    1≤source.clock ∧ post=setVarHOLFinite (ofString "nz") (.val (.word (GasBudget.U256Zero.resultWord accumulator)))
      (bind {source with clock:=source.clock-1} "i" (BitVec.ofNat 64 (index+1))) := by
  have read : eval source increment=some (.val (.word (BitVec.ofNat 64 (index+1)))):=by
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have assigned:=StateSteps.assign_execute source "i" increment _ _ i read
  rw [finishIteration,evaluateHOLFiniteState_seq_line780,assigned] at normal
  let advanced:=bind source "i" (BitVec.ofNat 64 (index+1))
  have nextAcc : advanced.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator):=
    (bind_lookup_other source "i" "acc" _ (by decide)).trans acc
  have args : evalListHOLFinite advanced (h:=fun query=>Classical.propDecidable (advanced.memaddrs query)) [localVar "acc"]=some [RlpWrite.U256Value.tuple accumulator]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nextAcc]
  obtain ⟨funded,postEq⟩:=GasBudget.U256Zero.assigned_normal advanced post accumulator installed (ofString "nz") [localVar "acc"] args normal
  exact ⟨funded,postEq⟩

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.finish_iteration_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.finish_iteration_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- All outcomes of the literal assigned division and counter/zero suffix
are charged from the current concrete denominator and physical workspace. -/
theorem after_denominator_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (di : source.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index)))) :
    source.clock-(evaluateHOLFiniteState source afterDenominator).2.clock≤329 := by
  have bounds:=denominator_bounds index positive bounded
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "p",localVar "di"]=
      some [RlpWrite.U256Value.tuple product,RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,p,di]
  exact ClockCost.sequence_current source
    (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_div") [localVar "p",localVar "di"]) finishIteration 328 1
    (UDivMod.WideDigits.U256Word.divide_call_cost source base (denominator index) product context installed bounds.1 bounds.2.2
      (some (some (ofString "acc"))) [localVar "p",localVar "di"] args) (finish_iteration_cost source.code installed)

structure DivisionResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad)
    (index : Nat) (quotient : Quad) : Prop where
  state : post={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}
  acc : post.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple quotient)
  i : post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1))))
  nz : post.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord quotient)))
  quotientEq : UDivMod.WideDigits.quadNumber quotient=UDivMod.WideDigits.quadNumber product/(index*11684671)
  other : ∀ key : MlS,key≠ofString "acc"→key≠ofString "i"→key≠ofString "nz"→post.locals.lookup key=source.locals.lookup key
  away : ∀ query,(∀ current,current<17→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .normalizedNumerator) current)→
    (∀ current,current<8→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .normalizedDivisor) current)→
    (∀ current,current<16→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .quotient) current)→
    (∀ current,current<8→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .remainder) current)→
    (∀ current,current<8→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .divisor) current)→
    (∀ current,current<8→query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base .numerator) current)→post.memory query=source.memory query
  cost : source.clock-post.clock≤329

/-- The real assigned division and final two instructions derive the next
Taylor term, actual increment and actual zero flag from one normal suffix. -/
theorem after_denominator_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (di : source.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source afterDenominator=(none,post)) :
    ∃ quotient,DivisionResult source post base product index quotient := by
  have bounds:=denominator_bounds index positive bounded
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "p",localVar "di"]=
      some [RlpWrite.U256Value.tuple product,RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,p,di]
  obtain ⟨middle,divisionRun,finishRun⟩:=sequence_none source post
    (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_div") [localVar "p",localVar "di"]) finishIteration normal
  obtain ⟨quotient,funded,canonical,numeric,memory,divisionPrice⟩:=UDivMod.WideDigits.U256Word.divide_assigned_normal source middle base (denominator index) product
    context installed bounds.1 bounds.2.2 (ofString "acc") [localVar "p",localVar "di"] args divisionRun
  have nextCode : OriginalCode.Installed middle.code:=by rw [canonical];exact installed
  have nextI : middle.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    rw [canonical]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  have nextAcc : middle.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple quotient):=by
    rw [canonical]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  obtain ⟨finishFunded,postEq⟩:=finish_iteration_normal middle post index quotient nextCode nextI nextAcc finishRun
  have finalFrame : post={middle with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [postEq];rfl
  have combined:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) canonical
  have quotientEq:=numeric
  rw [denominator_number index bounded] at quotientEq
  have price:=after_denominator_cost source base product index context installed positive bounded p di
  rw [normal] at price
  refine ⟨quotient,⟨finalFrame.trans combined,?_,?_,?_,quotientEq,?_,?_,price⟩⟩
  · rw [postEq]
    simpa [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using nextAcc
  · rw [postEq]
    simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
  · rw [postEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  · intro key notAcc notI notNz
    rw [postEq,canonical]
    simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notAcc,notI,notNz,Ne.symm notAcc,Ne.symm notI,Ne.symm notNz]
  · intro query outsideUN outsideVN outsideQ outsideR outsideV outsideU
    have retained : post.memory=middle.memory:=by rw [postEq];rfl
    rw [retained]
    exact memory query outsideUN outsideVN outsideQ outsideR outsideV outsideU

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_denominator_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_denominator_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal denominator multiplication supplies the precise word
passed to the following actual division, plus the derived inner result. -/
theorem after_word_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (di : source.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index))))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source afterWord=(none,post)) :
    ∃ middle quotient,2≤source.clock ∧ middle=setVarHOLFinite (ofString "di")
      (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))) {source with clock:=source.clock-2} ∧
      DivisionResult middle post base product index quotient := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "di",localVar "den"]=
      some [RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index)),RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,di,den]
  obtain ⟨middle,multiplyRun,divisionRun⟩:=sequence_none source post
    (.call (some (some (.local,ofString "di"),none)) (ofString "u256_mul") [localVar "di",localVar "den"]) afterDenominator normal
  obtain ⟨funded,middleEq⟩:=GasBudget.U256Multiply.word_assigned_normal source middle (BitVec.ofNat 64 index) 11684671#64 installed (ofString "di") [localVar "di",localVar "den"] args multiplyRun
  rw [denominator_product index bounded] at middleEq
  have nextContext : UDivMod.WideDigits.Workspace.Context middle base:=by
    refine ⟨?_,?_,context.arena,context.aligned⟩
    · rw [middleEq]
      exact context.global
    · rw [middleEq]
      exact context.domain
  have nextCode : OriginalCode.Installed middle.code:=by rw [middleEq];exact installed
  have nextP : middle.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product):=by
    rw [middleEq]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using p
  have nextDi : middle.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))):=by
    rw [middleEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have nextI : middle.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    rw [middleEq]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  obtain ⟨quotient,result⟩:=after_denominator_normal middle post base product index nextContext nextCode positive bounded nextP nextDi nextI divisionRun
  exact ⟨middle,quotient,funded,middleEq,result⟩

/-- Price the denominator multiplication's actual reached continuation;
no value, successful child or sufficient future division clock is assumed. -/
theorem after_word_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (di : source.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index))))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64))) :
    source.clock-(evaluateHOLFiniteState source afterWord).2.clock≤331 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "di",localVar "den"]=
      some [RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index)),RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,di,den]
  apply ClockCost.sequence_reached_current source
    (.call (some (some (.local,ofString "di"),none)) (ofString "u256_mul") [localVar "di",localVar "den"]) afterDenominator 2 329
    (GasBudget.U256Multiply.word_call_cost source (BitVec.ofNat 64 index) 11684671#64 installed (some (some (ofString "di"))) [localVar "di",localVar "den"] args)
  intro middle normal
  obtain ⟨funded,middleEq⟩:=GasBudget.U256Multiply.word_assigned_normal source middle (BitVec.ofNat 64 index) 11684671#64 installed (ofString "di") [localVar "di",localVar "den"] args normal
  rw [denominator_product index bounded] at middleEq
  have nextContext : UDivMod.WideDigits.Workspace.Context middle base:=by
    refine ⟨?_,?_,context.arena,context.aligned⟩
    · rw [middleEq]
      exact context.global
    · rw [middleEq]
      exact context.domain
  have nextCode : OriginalCode.Installed middle.code:=by rw [middleEq];exact installed
  have nextP : middle.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product):=by
    rw [middleEq]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using p
  have nextDi : middle.locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index))):=by
    rw [middleEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  exact after_denominator_cost middle base product index nextContext nextCode positive bounded nextP nextDi

def wordEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) :=
  setVarHOLFinite (ofString "di") (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index))) {source with clock:=source.clock-1}

/-- The original from-word, multiplication, assigned division, increment
and actual zero test are bounded together at every potentially active index. -/
theorem division_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source divisionStep).2.clock≤332 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "i"]=some [.val (.word (BitVec.ofNat 64 index))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,i]
  obtain ⟨callee,called,w⟩:=word_environment source.code.lookup (ofString "u256_from_word") (ofString "w") GasBudget.U256Multiply.fromWordBody
    RlpWrite.U256Value.tupleShape (BitVec.ofNat 64 index) (GasBudget.U256Multiply.from_word_code source.code installed)
  have bodyPrice:=GasBudget.ArithmeticEffects.price_u256_from_word source.code (GasBudget.ArithmeticEffects.current_environment source.code installed)
  apply ClockCost.scoped_reached_current source "di" RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "i"] _
    GasBudget.U256Multiply.fromWordBody afterWord callee RlpWrite.U256Value.tupleShape 0 331 args called (bodyPrice _ rfl)
  intro target returned run valid
  have expected:=GasBudget.U256Multiply.from_word_execute (callEntryStateHOLFinite source callee) (BitVec.ofNat 64 index) w
  have targetEq : target=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee):=congrArg Prod.snd (run.symm.trans expected)
  have returnedEq : returned=RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index)):=by
    have same:=congrArg Prod.fst (run.symm.trans expected)
    cases same
    rfl
  have entryEq : CallNormal.continuationEntry source target "di" returned=wordEntry source index:=by rw [targetEq,returnedEq];rfl
  have readyContext : UDivMod.WideDigits.Workspace.Context (wordEntry source index) base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have readyP : (wordEntry source index).locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product):=by
    simpa [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using p
  have readyDi : (wordEntry source index).locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index))):=by
    simp [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have readyDen : (wordEntry source index).locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have price:=after_word_cost (wordEntry source index) base product index readyContext installed positive bounded readyP readyDi readyDen
  rw [entryEq]
  have clock : target.clock=(wordEntry source index).clock:=by rw [targetEq];rfl
  rw [clock]
  exact price

/-- A real completed division step exposes its actual conversion and
multiplication states, numeric next term and restored output counter/flag. -/
theorem division_step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (product : Quad) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (p : source.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source divisionStep=(none,post)) :
    ∃ middle inner quotient,1≤source.clock ∧ 2≤(wordEntry source index).clock ∧
      middle=setVarHOLFinite (ofString "di") (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords (denominator index)))
        {wordEntry source index with clock:=(wordEntry source index).clock-2} ∧
      DivisionResult middle inner base product index quotient ∧ post=restore source "di" inner ∧
      post.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple quotient) ∧
      post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))) ∧
      post.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord quotient))) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "i"]=some [.val (.word (BitVec.ofNat 64 index))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,i]
  obtain ⟨inner,funded,run,restored⟩:=GasBudget.U256Multiply.from_word_call_normal source post (BitVec.ofNat 64 index) installed "di" [localVar "i"] afterWord args normal
  have readyContext : UDivMod.WideDigits.Workspace.Context (wordEntry source index) base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have readyP : (wordEntry source index).locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple product):=by
    simpa [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using p
  have readyDi : (wordEntry source index).locals.lookup (ofString "di")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad (BitVec.ofNat 64 index))):=by
    simp [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have readyDen : (wordEntry source index).locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have readyI : (wordEntry source index).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    simpa [wordEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  obtain ⟨middle,quotient,mulFunded,middleEq,result⟩:=after_word_normal (wordEntry source index) inner base product index readyContext installed
    positive bounded readyP readyDi readyDen readyI run
  refine ⟨middle,inner,quotient,funded,mulFunded,middleEq,result,restored,?_,?_,?_⟩
  · rw [restored]
    exact (restore_lookup_other source inner "di" "acc" (by decide)).trans result.acc
  · rw [restored]
    exact (restore_lookup_other source inner "di" "i" (by decide)).trans result.i
  · rw [restored]
    exact (restore_lookup_other source inner "di" "nz" (by decide)).trans result.nz

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_word_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_word_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.division_step_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.division_step_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem overflow_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accumulator : Quad) (numerator : BitVec 64)
    (prod : source.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator)) :
    eval source overflowTest=some (.val (.word (if (GasBudget.U256Multiply.scalarFourth accumulator numerator).1 |||
      (GasBudget.U256Multiply.scalarFourth accumulator numerator).2=0#64 then 0#64 else 1#64))) := by
  by_cases zero : (GasBudget.U256Multiply.scalarFourth accumulator numerator).1 ||| (GasBudget.U256Multiply.scalarFourth accumulator numerator).2=0#64
  all_goals simp [eval,overflowTest,localVar,evalHOLExact,evalListHOLExact,toExact,prod,GasBudget.U256Multiply.scalarValue,
    valueIsWord,valueWord,wordOpHOL,wordOp,OrOp.or,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

/-- A continuing real overflow guard necessarily skipped its trap. The
absence of overflow is derived from that same execution. -/
theorem overflow_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (accumulator : Quad) (numerator : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (prod : source.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator))
    (normal : evaluateHOLFiniteState source overflowGuard=(none,post)) :
    (GasBudget.U256Multiply.scalarFourth accumulator numerator).1 ||| (GasBudget.U256Multiply.scalarFourth accumulator numerator).2=0#64 ∧ post=source := by
  have tested:=overflow_read source accumulator numerator prod
  by_cases fits : (GasBudget.U256Multiply.scalarFourth accumulator numerator).1 ||| (GasBudget.U256Multiply.scalarFourth accumulator numerator).2=0#64
  · simp only [eval,if_pos fits] at tested
    have skipped : evaluateHOLFiniteState source overflowGuard=(none,source):=by
      rw [overflowGuard,evaluateHOLFiniteState_ite,tested]
      simp [evaluateHOLFiniteState_skip]
    exact ⟨fits,congrArg Prod.snd (normal.symm.trans skipped)⟩
  · simp only [eval,if_neg fits] at tested
    rw [overflowGuard,evaluateHOLFiniteState_ite,tested] at normal
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)] at normal
    exact (Trap.call_not_normal source post [.const 3#64] 3#64 (Trap.original_code source.code installed) rfl normal).elim

/-- The real low-product declaration reads exactly the four physical low
limbs of the actual eight-word multiply result. -/
theorem low_product_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accumulator : Quad) (numerator : BitVec 64)
    (prod : source.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator)) :
    eval source lowProduct=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)) := by
  simp [eval,lowProduct,localVar,evalHOLExact,evalListHOLExact,toExact,prod,GasBudget.U256Multiply.scalarValue,
    GasBudget.U256Multiply.scalarLow,RlpWrite.U256Value.tuple,
    show ((3 : Fin 4) : Nat)≠1 by decide,show ((3 : Fin 4) : Nat)≠2 by decide]

/-- The original overflow trap and low-product/division route cost their
maximum: the genuine trap cannot fall through and costs only one tick. -/
theorem after_product_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (prod : source.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source afterProduct).2.clock≤332 := by
  let ready:=setVarHOLFinite (ofString "p") (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)) source
  have readyContext : UDivMod.WideDigits.Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have readyP : ready.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)):=by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have readyDen : ready.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have readyI : ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  have back:=ClockCost.declared_value_current source (ofString "p") RlpWrite.U256Value.tupleShape lowProduct
    (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)) divisionStep 332 (low_product_read source accumulator numerator prod)
    (division_step_cost ready base (GasBudget.U256Multiply.scalarLow accumulator numerator) index readyContext installed positive bounded readyP readyDen readyI)
  have stops : (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "trap_with") [.const 3#64])).1≠none:=by
    intro noneResult
    have run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "trap_with") [.const 3#64])=
        (none,(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "trap_with") [.const 3#64])).2):=Prod.ext noneResult rfl
    exact Trap.call_not_normal source _ [.const 3#64] 3#64 (Trap.original_code source.code installed) rfl run
  exact ClockCost.stopping_guard_current source overflowTest (.call (some (none,none)) (ofString "trap_with") [.const 3#64])
    (.dec (ofString "p") RlpWrite.U256Value.tupleShape lowProduct divisionStep) 1 332 stops (Trap.call_price source.code installed _ source rfl) back

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.overflow_read
#print axioms InitECandidate.Solver.Input.TaylorCurrent.overflow_guard_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.low_product_read
#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_product_cost

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Result of the unchanged product guard and arithmetic suffix at its
actual current product: the natural recurrence is a derived output fact. -/
structure ProductResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (accumulator : Quad) (numerator : BitVec 64) (index : Nat) (quotient : Quad) : Prop where
  state : post={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}
  fits : UDivMod.WideDigits.quadNumber accumulator*numerator.toNat<2^256
  acc : post.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple quotient)
  i : post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1))))
  nz : post.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord quotient)))
  recurrence : UDivMod.WideDigits.quadNumber quotient=
    UDivMod.WideDigits.quadNumber accumulator*numerator.toNat/(index*11684671)
  other : ∀ key : String,ofString key≠ofString "acc"→ ofString key≠ofString "i"→ ofString key≠ofString "nz"→
    ofString key≠ofString "p"→ ofString key≠ofString "di"→post.locals.lookup (ofString key)=source.locals.lookup (ofString key)
  away : ∀ query,(∀ buffer current,current<UDivMod.WideDigits.Workspace.count buffer→
    query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base buffer) current)→post.memory query=source.memory query
  cost : source.clock-post.clock≤332

/-- A genuinely completed guarded product suffix derives non-overflow,
the true natural next term and its actual counter/zero flag. All reads,
scopes, workspace writes and child returns come from that same execution. -/
theorem after_product_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (prod : source.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source afterProduct=(none,post)) :
    ∃ quotient,ProductResult source post base accumulator numerator index quotient := by
  obtain ⟨guardPost,guardRun,declaredRun⟩:=sequence_none source post overflowGuard (.dec (ofString "p") RlpWrite.U256Value.tupleShape lowProduct divisionStep) normal
  obtain ⟨fits,guardEq⟩:=overflow_guard_normal source guardPost accumulator numerator installed prod guardRun
  subst guardPost
  obtain ⟨declared,inner,read,valid,stepRun,restoredP⟩:=CallNormal.declaration_continuing_entry source post "p" RlpWrite.U256Value.tupleShape lowProduct divisionStep declaredRun
  have actualRead:=low_product_read source accumulator numerator prod
  have valueEq : declared=RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator):=Option.some.inj (read.symm.trans actualRead)
  subst declared
  let pEntry:=setVarHOLFinite (ofString "p") (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)) source
  have entryContext : UDivMod.WideDigits.Workspace.Context pEntry base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have entryP : pEntry.locals.lookup (ofString "p")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.scalarLow accumulator numerator)):=by
    simp [pEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have entryDen : pEntry.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [pEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have entryI : pEntry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    simpa [pEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  obtain ⟨divisionSource,divisionPost,quotient,wordFunded,multiplyFunded,divisionSourceEq,division,restoredDi,accCell,iCell,nzCell⟩:=
    division_step_normal pEntry inner base (GasBudget.U256Multiply.scalarLow accumulator numerator) index entryContext installed positive bounded entryP entryDen entryI stepRun
  have finalFrame : post={divisionPost with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [restoredP,restoredDi];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) division.state
  rw [divisionSourceEq] at projected
  change {divisionPost with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have fitsNumber:= (GasBudget.U256Multiply.scalar_overflow accumulator numerator).mp fits
  have fullProduct:=GasBudget.U256Multiply.scalar_low_product accumulator numerator fits
  change UDivMod.WideDigits.quadNumber (GasBudget.U256Multiply.scalarLow accumulator numerator)=UDivMod.WideDigits.quadNumber accumulator*numerator.toNat at fullProduct
  have recurrence:=division.quotientEq
  rw [fullProduct] at recurrence
  have price:=after_product_cost source base accumulator numerator index context installed positive bounded prod den i
  rw [normal] at price
  refine ⟨quotient,⟨finalFrame.trans projected,fitsNumber,?_,?_,?_,recurrence,?_,?_,price⟩⟩
  · rw [restoredP]
    exact (restore_lookup_other source inner "p" "acc" (by decide)).trans accCell
  · rw [restoredP]
    exact (restore_lookup_other source inner "p" "i" (by decide)).trans iCell
  · rw [restoredP]
    exact (restore_lookup_other source inner "p" "nz" (by decide)).trans nzCell
  · intro key notAcc notI notNz notP notDi
    rw [restoredP,restore_lookup_other source inner "p" key notP,restoredDi,restore_lookup_other pEntry divisionPost "di" key notDi,
      division.other (ofString key) notAcc notI notNz,divisionSourceEq]
    simp [wordEntry,pEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notP,notDi,Ne.symm notP,Ne.symm notDi]
  · intro query outside
    have postMemory : post.memory=divisionPost.memory:=by rw [restoredP,restoredDi];rfl
    have entryMemory : divisionSource.memory=source.memory:=by rw [divisionSourceEq];rfl
    rw [postMemory]
    have kept:=division.away query (outside .normalizedNumerator) (outside .normalizedDivisor) (outside .quotient)
      (outside .remainder) (outside .divisor) (by intro current inside;exact outside .numerator current (by change current<16;omega))
    exact kept.trans (congrFun entryMemory query)

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_product_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def outAdd : ProgHOL 64:=.call (some (some (.local,ofString "out"),none)) (ofString "u256_add") [localVar "out",localVar "acc"]
def multiplyStep : ProgHOL 64:=.decCall (ofString "prod") (.comb [.one,.one,.one,.one,.one,.one,.one,.one])
  (ofString "u256_mul_full") [localVar "acc",localVar "num"] afterProduct

theorem iteration_split : iteration=.seq outAdd multiplyStep := rfl

private theorem out_add_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code outAdd 1 := by
  let kind:=GasBudget.ArithmeticEffects.Kind.u256_add
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  exact ClockCost.call_body code (some (some (ofString "out"))) (ofString "u256_add") [localVar "out",localVar "acc"]
    kind.signature.1 kind.body kind.signature.2.2 0 (environment kind) (GasBudget.ArithmeticEffects.price_u256_add code environment)

private theorem out_add_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source outAdd=(none,target)) :
    LocalEffects.erase target=LocalEffects.erase source := by
  let kind:=GasBudget.ArithmeticEffects.Kind.u256_add
  have environment:=GasBudget.ArithmeticEffects.current_environment source.code installed
  have pure:=LocalEffects.call_body source.code (some (some (ofString "out"))) (ofString "u256_add") [localVar "out",localVar "acc"]
    kind.signature.1 kind.body kind.signature.2.2 (environment kind) (GasBudget.ArithmeticEffects.original_preserves kind source.code environment)
  have frame:=pure source rfl
  change LocalEffects.erase (evaluateHOLFiniteState source outAdd).2=LocalEffects.erase source at frame
  simpa only [normal] using frame

private theorem out_add_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS)
    (other : key≠ofString "out") (normal : evaluateHOLFiniteState source outAdd=(none,target)) :
    target.locals.lookup key=source.locals.lookup key := by
  have safe : LocalPrefix key outAdd:=.call (some (ofString "out")) (ofString "u256_add") [localVar "out",localVar "acc"]
    (by intro name same;cases Option.some.inj same;exact other)
  have kept:=(safe.summary_full source).1 (by rw [normal])
  simpa only [normal] using kept

private theorem context_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (frame : LocalEffects.erase target=LocalEffects.erase source) :
    UDivMod.WideDigits.Workspace.Context target base := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change target.memaddrs=source.memaddrs at domain
  exact ⟨by rw [globals];exact context.global,domain.trans context.domain,context.arena,context.aligned⟩

def productEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accumulator : Quad) (numerator : BitVec 64) :=
  setVarHOLFinite (ofString "prod") (GasBudget.U256Multiply.scalarValue accumulator numerator) {source with clock:=source.clock-17}

/-- The genuine full multiply call supplies the exact current product for
the checked guard/suffix; every stopped and short-clock outcome is priced. -/
theorem multiply_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source multiplyStep).2.clock≤349 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc",localVar "num"]=
      some [RlpWrite.U256Value.tuple accumulator,RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc,num]
  obtain ⟨callee,called,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_mul_full") GasBudget.U256Multiply.fullBody
    (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) accumulator (GasBudget.U256Multiply.wordQuad numerator) (GasBudget.U256Multiply.full_code source.code installed)
  have price:=GasBudget.ArithmeticEffects.price_u256_mul_full source.code (GasBudget.ArithmeticEffects.current_environment source.code installed)
  apply ClockCost.scoped_reached_current source "prod" (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) (ofString "u256_mul_full") [localVar "acc",localVar "num"] _
    GasBudget.U256Multiply.fullBody afterProduct callee (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) 16 332 args called (price _ rfl)
  intro target returned run valid
  obtain ⟨returnedEq,funded,entryEq⟩:=GasBudget.U256Multiply.scalar_resume source target "prod" accumulator numerator installed GasBudget.U256Multiply.fullBody callee
    (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) called returned run
  let ready:=productEntry source accumulator numerator
  have readyContext : UDivMod.WideDigits.Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have prod : ready.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator):=by
    simp [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have nextDen : ready.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have nextI : ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    simpa [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  have back:=after_product_cost ready base accumulator numerator index readyContext installed positive bounded prod nextDen nextI
  rw [entryEq]
  have boundaryClock:=congrArg PanSemStateFiniteExact.clock entryEq
  have clock : target.clock=ready.clock:=boundaryClock
  rw [clock]
  exact back

/-- A real normal full-multiply scope derives the exact scalar product,
completed guarded arithmetic result and actual restoration of prod. -/
theorem multiply_step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source multiplyStep=(none,post)) :
    ∃ inner quotient,17≤source.clock ∧ ProductResult (productEntry source accumulator numerator) inner base accumulator numerator index quotient ∧
      post=restore source "prod" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc",localVar "num"]=
      some [RlpWrite.U256Value.tuple accumulator,RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc,num]
  obtain ⟨callee,called,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_mul_full") GasBudget.U256Multiply.fullBody
    (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) accumulator (GasBudget.U256Multiply.wordQuad numerator) (GasBudget.U256Multiply.full_code source.code installed)
  obtain ⟨callFunded,target,returned,inner,run,valid,tailRun,restored⟩:=CallNormal.scoped_none source post "prod" (.comb [.one,.one,.one,.one,.one,.one,.one,.one])
    (ofString "u256_mul_full") [localVar "acc",localVar "num"] _ GasBudget.U256Multiply.fullBody afterProduct callee (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) args called normal
  obtain ⟨returnedEq,funded,entryEq⟩:=GasBudget.U256Multiply.scalar_resume source target "prod" accumulator numerator installed GasBudget.U256Multiply.fullBody callee
    (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) called returned run
  rw [entryEq] at tailRun
  let ready:=productEntry source accumulator numerator
  have readyContext : UDivMod.WideDigits.Workspace.Context ready base:=⟨context.global,context.domain,context.arena,context.aligned⟩
  have prod : ready.locals.lookup (ofString "prod")=some (GasBudget.U256Multiply.scalarValue accumulator numerator):=by
    simp [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have nextDen : ready.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)):=by
    simpa [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using den
  have nextI : ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
    simpa [ready,productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  obtain ⟨quotient,result⟩:=after_product_normal ready inner base accumulator numerator index readyContext installed positive bounded prod nextDen nextI tailRun
  exact ⟨inner,quotient,funded,result,restored⟩

/-- Every outcome of the complete unchanged Taylor body iteration costs
at most350source ticks at a current valid counter/accumulator entry. -/
theorem iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤350 := by
  rw [iteration_split]
  apply ClockCost.sequence_reached_current source outAdd multiplyStep 1 349 (out_add_cost source.code installed source rfl)
  intro middle normal
  have frame:=out_add_frame source middle installed normal
  have nextContext:=context_of_erase source middle base context frame
  have nextCode : OriginalCode.Installed middle.code:=by rw [LocalEffects.code_of_erase source middle frame];exact installed
  exact multiply_step_cost middle base accumulator numerator index nextContext nextCode positive bounded
    ((out_add_other source middle (ofString "acc") (by decide) normal).trans acc)
    ((out_add_other source middle (ofString "num") (by decide) normal).trans num)
    ((out_add_other source middle (ofString "den") (by decide) normal).trans den)
    ((out_add_other source middle (ofString "i") (by decide) normal).trans i)

structure IterationResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (accumulator : Quad) (numerator : BitVec 64) (index : Nat) (quotient : Quad) : Prop where
  state : post={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}
  fits : UDivMod.WideDigits.quadNumber accumulator*numerator.toNat<2^256
  acc : post.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple quotient)
  i : post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1))))
  nz : post.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord quotient)))
  recurrence : UDivMod.WideDigits.quadNumber quotient=UDivMod.WideDigits.quadNumber accumulator*numerator.toNat/(index*11684671)
  other : ∀ key : String,ofString key≠ofString "acc"→ ofString key≠ofString "i"→ ofString key≠ofString "nz"→
    ofString key≠ofString "out"→ ofString key≠ofString "prod"→ ofString key≠ofString "p"→ ofString key≠ofString "di"→
    post.locals.lookup (ofString key)=source.locals.lookup (ofString key)
  away : ∀ query,(∀ buffer current,current<UDivMod.WideDigits.Workspace.count buffer→
    query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base buffer) current)→post.memory query=source.memory query
  cost : source.clock-post.clock≤350

/-- An actual continuing whole iteration derives the true recurrence and
next guard/counter from its real addition, multiply, trap test and division. -/
theorem iteration_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (accumulator : Quad) (numerator : BitVec 64) (index : Nat)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (positive : 0<index) (bounded : index≤1280)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source iteration=(none,post)) :
    ∃ quotient,IterationResult source post base accumulator numerator index quotient := by
  obtain ⟨middle,addRun,multiplyRun⟩:=sequence_none source post outAdd multiplyStep normal
  have frame:=out_add_frame source middle installed addRun
  have nextContext:=context_of_erase source middle base context frame
  have nextCode : OriginalCode.Installed middle.code:=by rw [LocalEffects.code_of_erase source middle frame];exact installed
  obtain ⟨inner,quotient,funded,result,restored⟩:=multiply_step_normal middle post base accumulator numerator index nextContext nextCode positive bounded
    ((out_add_other source middle (ofString "acc") (by decide) addRun).trans acc)
    ((out_add_other source middle (ofString "num") (by decide) addRun).trans num)
    ((out_add_other source middle (ofString "den") (by decide) addRun).trans den)
    ((out_add_other source middle (ofString "i") (by decide) addRun).trans i) multiplyRun
  have middleFrame : middle={source with locals:=middle.locals,clock:=middle.clock}:=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=middle.locals,clock:=middle.clock}) frame
  have finalFrame : post={inner with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [restored];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  rw [middleFrame] at projected
  change {inner with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have price:=iteration_cost source base accumulator numerator index context installed positive bounded acc num den i
  rw [normal] at price
  refine ⟨quotient,⟨finalFrame.trans projected,result.fits,?_,?_,?_,result.recurrence,?_,?_,price⟩⟩
  · rw [restored]
    exact (restore_lookup_other middle inner "prod" "acc" (by decide)).trans result.acc
  · rw [restored]
    exact (restore_lookup_other middle inner "prod" "i" (by decide)).trans result.i
  · rw [restored]
    exact (restore_lookup_other middle inner "prod" "nz" (by decide)).trans result.nz
  · intro key notAcc notI notNz notOut notProd notP notDi
    rw [restored,restore_lookup_other middle inner "prod" key notProd,result.other key notAcc notI notNz notP notDi]
    have saved : (productEntry middle accumulator numerator).locals.lookup (ofString key)=middle.locals.lookup (ofString key):=by
      simp [productEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notProd,Ne.symm notProd]
    exact saved.trans (out_add_other source middle (ofString key) notOut addRun)
  · intro query outside
    rw [restored]
    exact (result.away query outside).trans (congrFun (LocalEffects.memory_of_erase source middle frame) query)

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.iteration_split
#print axioms InitECandidate.Solver.Input.TaylorCurrent.multiply_step_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.multiply_step_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.iteration_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.iteration_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem unused_call (name : String) (function : MlS) (arguments : List (ExpHOL 64))
    (different : ofString "unused"≠ofString name) :
    LocalPrefix (ofString "unused") (.call (some (some (.local,ofString name),none)) function arguments) :=
  .call (some (ofString name)) function arguments (by intro actual same;cases Option.some.inj same;exact different)

/-- The literal iteration cannot escape with break, continue or a caller
return; real helper errors/traps/timeouts remain unrestricted. -/
theorem iteration_prefix : LocalPrefix (ofString "unused") iteration := by
  have finish : LocalPrefix (ofString "unused") finishIteration:=.seq
    (.assign (ofString "i") increment (by decide)) (unused_call "nz" (ofString "u256_is_zero") [localVar "acc"] (by decide))
  have divided : LocalPrefix (ofString "unused") afterDenominator:=.seq
    (unused_call "acc" (ofString "u256_div") [localVar "p",localVar "di"] (by decide)) finish
  have multiplied : LocalPrefix (ofString "unused") afterWord:=.seq
    (unused_call "di" (ofString "u256_mul") [localVar "di",localVar "den"] (by decide)) divided
  have converted : LocalPrefix (ofString "unused") divisionStep:=.decCall (ofString "di") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "i"] (by decide) multiplied
  have low : LocalPrefix (ofString "unused") (.dec (ofString "p") RlpWrite.U256Value.tupleShape lowProduct divisionStep):=
    .dec (ofString "p") RlpWrite.U256Value.tupleShape lowProduct (by decide) converted
  have guarded : LocalPrefix (ofString "unused") overflowGuard:=.ite overflowTest
    (.call none (ofString "trap_with") [.const 3#64] (by intro name impossible;cases impossible)) .skip
  have product : LocalPrefix (ofString "unused") afterProduct:=.seq guarded low
  have full : LocalPrefix (ofString "unused") multiplyStep:=.decCall (ofString "prod") (.comb [.one,.one,.one,.one,.one,.one,.one,.one])
    (ofString "u256_mul_full") [localVar "acc",localVar "num"] (by decide) product
  exact .seq (unused_call "out" (ofString "u256_add") [localVar "out",localVar "acc"] (by decide)) full

/-- The loop invariant records only already executed terms. The current
term may be zero; all earlier terms were positive when their guards ran. -/
structure LoopModel (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (numerator : BitVec 64)
    (index : Nat) (accumulator : Quad) (values : Nat→Nat) : Prop where
  positive : 0<index
  bounded : index≤1281
  context : UDivMod.WideDigits.Workspace.Context source base
  installed : OriginalCode.Installed source.code
  acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator)
  num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator))
  den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64))
  i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator)))
  current : values (index-1)=UDivMod.WideDigits.quadNumber accumulator
  past : ∀ step,step<index-1→0<values step ∧ values step<2^256
  recurrence : ∀ step,step<index-1→values (step+1)=values step*numerator.toNat/(11684671*(step+1))
  state : source={origin with
    locals:=source.locals,memory:=source.memory,clock:=source.clock}
  away : ∀ query,(∀ buffer current,current<UDivMod.WideDigits.Workspace.count buffer→
    query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base buffer) current)→source.memory query=origin.memory query

theorem LoopModel.withClock {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values) (clock : Nat) :
    LoopModel origin {source with clock:=clock} base numerator index accumulator values := by
  refine ⟨model.positive,model.bounded,⟨model.context.global,model.context.domain,model.context.arena,model.context.aligned⟩,model.installed,
    model.acc,model.num,model.den,model.i,model.nz,model.current,model.past,model.recurrence,?_,model.away⟩
  exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=clock}) model.state

theorem loop_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accumulator : Quad)
    (nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator)))) :
    eval source loopTest=some (.val (.word (if 0<UDivMod.WideDigits.quadNumber accumulator then 1#64 else 0#64))) := by
  by_cases positive : 0<UDivMod.WideDigits.quadNumber accumulator
  · have zero:=(GasBudget.U256Zero.resultWord_zero accumulator).mpr positive
    simp [eval,loopTest,localVar,evalHOLExact,toExact,nz,zero,positive,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have nonzero : GasBudget.U256Zero.resultWord accumulator≠0#64:=by
      intro zero
      exact positive ((GasBudget.U256Zero.resultWord_zero accumulator).mp zero)
    simp [eval,loopTest,localVar,evalHOLExact,toExact,nz,nonzero,positive,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The checked finite positive-prefix arithmetic derives the current
active index range; the loop does not assume a future iteration limit. -/
theorem LoopModel.active_index {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values)
    (positive : 0<UDivMod.WideDigits.quadNumber accumulator) : index≤1280 := by
  have terms : ∀ step≤index-1,0<values step ∧ values step<2^256:=by
    intro step inside
    by_cases earlier : step<index-1
    · exact model.past step earlier
    · have same : step=index-1:=by omega
      rw [same,model.current]
      exact ⟨positive,GasBudget.U256Zero.number_lt accumulator⟩
  have short:=GeometricLoop.taylor_positive_prefix values numerator.toNat 11684671 (index-1) (by decide) terms model.recurrence
  have starts:=model.positive
  omega

theorem LoopModel.active {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values)
    (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) loopTest=some (.val (.word word)))
    (nonzero : word≠0#64) : 0<UDivMod.WideDigits.quadNumber accumulator ∧ index≤1280 := by
  have tested:=loop_test_read source accumulator model.nz
  simp only [UDivMod.finite_eval] at read
  have positive : 0<UDivMod.WideDigits.quadNumber accumulator:=by
    by_contra zero
    rw [if_neg zero] at tested
    have same : word=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans tested
    exact nonzero same
  exact ⟨positive,model.active_index positive⟩

def loopRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  1281-(CounterFlow.counterWord source (ofString "i")).toNat

theorem LoopModel.rank {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values) :
    loopRank source=1281-index := by
  have bound:=model.bounded
  have encoded : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [loopRank,CounterFlow.counterWord,model.i,valueWord,encoded]

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.iteration_prefix
#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.withClock
#print axioms InitECandidate.Solver.Input.TaylorCurrent.loop_test_read
#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.active_index
#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.active
#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.rank

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Extend only the already observed history by the actual normal body's
next term. The active guard supplies the former term's positivity. -/
theorem LoopModel.advance {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator quotient : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values)
    (positive : 0<UDivMod.WideDigits.quadNumber accumulator) (result : IterationResult source target base accumulator numerator index quotient) :
    LoopModel origin target base numerator (index+1) quotient
      (fun step=>if step=index then UDivMod.WideDigits.quadNumber quotient else values step) := by
  have activeBound:=model.active_index positive
  have starts:=model.positive
  refine {
    positive:=by omega, bounded:=by omega, context:=?_, installed:=?_, acc:=result.acc,
    num:=(result.other "num" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.num,
    den:=(result.other "den" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.den,
    i:=result.i,nz:=result.nz,current:=?_,past:=?_,recurrence:=?_,state:=?_,away:=?_ }
  · exact ⟨by rw [result.state];exact model.context.global,by rw [result.state];exact model.context.domain,model.context.arena,model.context.aligned⟩
  · rw [result.state]
    exact model.installed
  · simp
  · intro step inside
    have before : step<index:=by omega
    simp only [if_neg (show step≠index by omega)]
    by_cases earlier : step<index-1
    · exact model.past step earlier
    · have same : step=index-1:=by omega
      rw [same,model.current]
      exact ⟨positive,GasBudget.U256Zero.number_lt accumulator⟩
  · intro step inside
    have before : step<index:=by omega
    simp only [if_neg (show step≠index by omega)]
    by_cases last : step+1=index
    · rw [if_pos last]
      have same : step=index-1:=by omega
      rw [same,model.current]
      simpa only [show index-1+1=index by omega,Nat.mul_comm] using result.recurrence
    · rw [if_neg last]
      exact model.recurrence step (by omega)
  · exact result.state.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
      locals:=target.locals,memory:=target.memory,clock:=target.clock}) model.state)
  · intro query outside
    exact (result.away query outside).trans (model.away query outside)

/-- The actual ticked body extends the same history and preserves the
whole model, deriving the counter bound from its actual guard. -/
theorem LoopModel.step {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    {index : Nat} {accumulator : Quad} {values : Nat→Nat} (model : LoopModel origin source base numerator index accumulator values)
    (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) loopTest=some (.val (.word word)))
    (nonzero : word≠0#64) (normal : evaluateHOLFiniteState (decClockHOLFinite source) iteration=(none,target)) :
    ∃ quotient,LoopModel origin target base numerator (index+1) quotient
      (fun step=>if step=index then UDivMod.WideDigits.quadNumber quotient else values step) := by
  obtain ⟨positive,bounded⟩:=model.active word read nonzero
  have ticked:=model.withClock (source.clock-1)
  obtain ⟨quotient,result⟩:=iteration_normal (decClockHOLFinite source) target base accumulator numerator index ticked.context ticked.installed
    ticked.positive bounded ticked.acc ticked.num ticked.den ticked.i normal
  exact ⟨quotient,ticked.advance positive result⟩

def invariant (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index accumulator values,LoopModel origin source base numerator index accumulator values

/-- The actual loop has at most the remaining1280iterations. Its rank
comes from the real i local and its bound from the observed recurrence. -/
theorem loop_model_cost (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (index : Nat) (accumulator : Quad) (values : Nat→Nat) (model : LoopModel origin source base numerator index accumulator values) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤351*(1281-index) := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant origin base numerator current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→
      word≠0#64→current.clock≠0→current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) iteration).2.clock≤350:=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨position,term,history,checked⟩:=valid
    obtain ⟨positive,bounded⟩:=checked.active word read nonzero
    have ticked:=checked.withClock (current.clock-1)
    exact iteration_cost (decClockHOLFinite current) base term numerator position ticked.context ticked.installed ticked.positive bounded ticked.acc ticked.num ticked.den ticked.i
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant origin base numerator current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→word≠0#64→
      0<loopRank current ∧ (current.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
        (output.1=none ∨ output.1=some .continue)→ invariant origin base numerator output.2 ∧ loopRank output.2<loopRank current):=by
    intro current codeEq valid word read nonzero
    obtain ⟨position,term,history,checked⟩:=valid
    obtain ⟨positive,bounded⟩:=checked.active word read nonzero
    refine ⟨by rw [checked.rank];omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have normalResult : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_prefix.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normalResult rfl
    obtain ⟨quotient,next⟩:=checked.step word read nonzero run
    refine ⟨⟨position+1,quotient,_,next⟩,?_⟩
    rw [next.rank,checked.rank]
    omega
  have bound:=ClockCost.ranked_loop_current source.code loopTest iteration 350 (invariant origin base numerator) loopRank priced progress source rfl
    ⟨index,accumulator,values,model⟩
  change source.clock-(evaluateHOLFiniteState source loop).2.clock≤351*loopRank source at bound
  rw [model.rank] at bound
  exact bound

/-- At its actual initial counter1and zero flag, the unchanged Taylor loop
spends at most449280source ticks on every outcome, with no assumed loop run. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64)))
    (nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator)))) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤449280 := by
  have model : LoopModel source source base numerator 1 accumulator (fun _=>UDivMod.WideDigits.quadNumber accumulator):=
    ⟨by decide,by decide,context,installed,acc,num,den,i,nz,rfl,(by intro step impossible;omega),(by intro step impossible;omega),rfl,(by intro query outside;rfl)⟩
  exact loop_model_cost source source base numerator 1 accumulator _ model

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.advance
#print axioms InitECandidate.Solver.Input.TaylorCurrent.LoopModel.step
#print axioms InitECandidate.Solver.Input.TaylorCurrent.loop_model_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.loop_cost

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- An actual normal loop exit retains its observed history, constants,
workspace and outside memory, and its real current accumulator is zero. -/
theorem loop_model_normal (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (index : Nat) (accumulator : Quad) (values : Nat→Nat) (model : LoopModel origin source base numerator index accumulator values)
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ finalIndex finalAccumulator finalValues,LoopModel origin post base numerator finalIndex finalAccumulator finalValues ∧
      UDivMod.WideDigits.quadNumber finalAccumulator=0 := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→ invariant origin base numerator current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) loopTest=some (.val (.word word))→
      word≠0#64→current.clock≠0→∀ target,evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,target)→ invariant origin base numerator target:=by
    intro current codeEq valid word read nonzero funded target run
    obtain ⟨position,term,history,checked⟩:=valid
    obtain ⟨quotient,next⟩:=checked.step word read nonzero run
    exact ⟨position+1,quotient,_,next⟩
  have retained:=loop_invariant_summary source.code (ofString "unused") loopTest iteration
    (fun current=>iteration_prefix.summary_full current) (invariant origin base numerator) transition source post rfl ⟨index,accumulator,values,model⟩ normal
  obtain ⟨finalIndex,finalAccumulator,finalValues,checked⟩:=retained
  have exited:=loop_normal_exit loopTest iteration (fun current=>(iteration_prefix.summary_full current).2.2.1) source post normal
  simp only [UDivMod.finite_eval] at exited
  have tested:=loop_test_read post finalAccumulator checked.nz
  have zero : UDivMod.WideDigits.quadNumber finalAccumulator=0:=by
    by_contra nonzero
    have positive : 0<UDivMod.WideDigits.quadNumber finalAccumulator:=by omega
    rw [if_pos positive] at tested
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using tested.symm.trans exited
    exact (show (1#64 : BitVec 64)≠0#64 by decide) impossible
  exact ⟨finalIndex,finalAccumulator,finalValues,checked,zero⟩

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.loop_model_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual normally exiting original loop keeps all protected data,
its fixed numerator/denominator and a zero actual accumulator. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64)))
    (nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator))))
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ finalIndex finalAccumulator finalValues,LoopModel source post base numerator finalIndex finalAccumulator finalValues ∧
      UDivMod.WideDigits.quadNumber finalAccumulator=0 := by
  have model : LoopModel source source base numerator 1 accumulator (fun _=>UDivMod.WideDigits.quadNumber accumulator):=
    ⟨by decide,by decide,context,installed,acc,num,den,i,nz,rfl,(by intro step impossible;omega),(by intro step impossible;omega),rfl,(by intro query outside;rfl)⟩
  exact loop_model_normal source source post base numerator 1 accumulator _ model normal

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.loop_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Successful original two-quad lookup derives the actual first four
words. Invalid argument shapes do not create a future callee entry. -/
private theorem first_quad (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function : MlS) (program : ProgHOL 64) (first : ValueHOL 64) (second : Quad)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (known : codeFn function=some ([(ofString "a",RlpWrite.U256Value.tupleShape),(ofString "b",RlpWrite.U256Value.tupleShape)],program,RlpWrite.U256Value.tupleShape))
    (called : lookupCodeHOLFinite codeFn function [first,RlpWrite.U256Value.tuple second]=some (actual,callee,shape)) :
    ∃ words : Quad,first=RlpWrite.U256Value.tuple words := by
  have raw:=lookupCodeHOLFinite_eq_some codeFn function [first,RlpWrite.U256Value.tuple second] actual callee shape called
  simp only [lookupCodeHOLExact,known] at raw
  split at raw
  · rename_i valid
    have checked : shapeEqHOL RlpWrite.U256Value.tupleShape (shapeOfHOLExact first)=true:=by
      simpa [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true] using valid.2.2
    exact RlpWrite.U256Value.of_shape first ((shapeEqHOL_eq_true _ _).mp checked).symm
  · cases raw

/-- The literal final assigned division costs at most316source ticks.
The running sum's shape is derived only if its current ABI lookup succeeds. -/
theorem final_division_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString "out"),none)) (ofString "u256_div") [localVar "out",localVar "den"])).2.clock≤316 := by
  have scalarDen : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords 11684671#64)):=by
    simpa only [GasBudget.U256Multiply.wordQuad_remainder] using den
  apply ClockCost.call_arguments_current source (some (some (ofString "out"))) (ofString "u256_div") [localVar "out",localVar "den"] 315
  intro values actual callee shape args called
  cases outCell : source.locals.lookup (ofString "out") with
  | none=>simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell] at args
  | some value=>
    have currentArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "out",localVar "den"]=
        some [value,RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords 11684671#64)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell,scalarDen]
    have valuesEq:=Option.some.inj (args.symm.trans currentArgs)
    subst values
    obtain ⟨accumulator,valueEq⟩:=first_quad source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody value
      (UDivMod.WideDigits.Single.remainderWords 11684671#64) actual callee shape (GasBudget.U256Division.div_code source.code installed) called
    subst value
    obtain ⟨expected,lookup,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody
      RlpWrite.U256Value.tupleShape accumulator (UDivMod.WideDigits.Single.remainderWords 11684671#64) (GasBudget.U256Division.div_code source.code installed)
    have same:=Option.some.inj (called.symm.trans lookup)
    have bodyEq : actual=GasBudget.U256Division.divBody:=congrArg Prod.fst same
    have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    rw [←calleeEq] at aCell bCell
    rw [bodyEq]
    have entryContext : UDivMod.WideDigits.Workspace.Context (callEntryStateHOLFinite source callee) base:=⟨context.global,context.domain,context.arena,context.aligned⟩
    exact UDivMod.WideDigits.U256.divide_cost (callEntryStateHOLFinite source callee) base 11684671#64 accumulator entryContext installed aCell bCell (by decide) (by decide)

/-- Includes the actual final return after division on every outcome. -/
theorem final_return_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64))) :
    source.clock-(evaluateHOLFiniteState source finalReturn).2.clock≤316 :=
  ClockCost.sequence_current source
    (.call (some (some (.local,ofString "out"),none)) (ofString "u256_div") [localVar "out",localVar "den"]) (.return (localVar "out")) 316 0
    (final_division_cost source base context installed den) (ClockCost.returned source.code _)

/-- Original loop and final division/return: all actual stopped outcomes
fit one allowance; the final entry is derived from that same normal loop. -/
theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64)))
    (nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator)))) :
    source.clock-(evaluateHOLFiniteState source afterZero).2.clock≤449596 := by
  apply ClockCost.sequence_reached_current source loop finalReturn 449280 316 (loop_cost source base numerator accumulator context installed acc num den i nz)
  intro middle normal
  obtain ⟨finalIndex,finalAccumulator,finalValues,model,zero⟩:=loop_normal source middle base numerator accumulator context installed acc num den i nz normal
  exact final_return_cost middle base model.context model.installed model.den

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.final_division_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.final_return_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_zero_cost

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal final call derives the current sum's actual four words,
its real quotient and the precise assigned caller state. -/
theorem final_division_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString "out"),none)) (ofString "u256_div") [localVar "out",localVar "den"])=(none,post)) :
    ∃ sum quotient,source.locals.lookup (ofString "out")=some (RlpWrite.U256Value.tuple sum) ∧
      UDivMod.WideDigits.quadNumber quotient=UDivMod.WideDigits.quadNumber sum/11684671 ∧
      post=setVarHOLFinite (ofString "out") (RlpWrite.U256Value.tuple quotient) {source with memory:=post.memory,clock:=post.clock} ∧
      (∀ query,(∀ buffer current,current<UDivMod.WideDigits.Workspace.count buffer→
        query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base buffer) current)→post.memory query=source.memory query) := by
  obtain ⟨funded,values,actual,callee,shape,target,returned,args,called,childRun,typed,postEq⟩:=CallNormal.local_data source post (ofString "out") (ofString "u256_div") [localVar "out",localVar "den"] normal
  have scalarDen : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords 11684671#64)):=by
    simpa only [GasBudget.U256Multiply.wordQuad_remainder] using den
  cases outCell : source.locals.lookup (ofString "out") with
  | none=>simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell] at args
  | some value=>
    have currentArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "out",localVar "den"]=
        some [value,RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords 11684671#64)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell,scalarDen]
    have valuesEq:=Option.some.inj (args.symm.trans currentArgs)
    subst values
    obtain ⟨sum,valueEq⟩:=first_quad source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody value
      (UDivMod.WideDigits.Single.remainderWords 11684671#64) actual callee shape (GasBudget.U256Division.div_code source.code installed) called
    subst value
    obtain ⟨quotient,callFunded,canonical,numeric,memory⟩:=UDivMod.WideDigits.U256.divide_assigned_normal source post base 11684671#64 sum context installed
      (by decide) (by decide) (ofString "out") [localVar "out",localVar "den"] currentArgs normal
    have clock:=congrArg PanSemStateFiniteExact.clock canonical
    change post.clock=source.clock-(UDivMod.WideDigits.U256.fullPrice sum 11684671#64+2) at clock
    rw [←clock] at canonical
    refine ⟨sum,quotient,rfl,numeric,canonical,?_⟩
    intro query outside
    exact memory query (outside .quotient) (outside .remainder) (outside .divisor)
      (by intro current inside;exact outside .numerator current (by change current<16;omega))

structure WorkspaceResult (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (price : Nat:=316) : Prop where
  state : post={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}
  away : ∀ query,(∀ buffer current,current<UDivMod.WideDigits.Workspace.count buffer→
    query≠UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer base buffer) current)→post.memory query=source.memory query
  cost : source.clock-post.clock≤price

/-- The actual final return contains the true assigned quotient quad and
preserves every nonlocal field and cell outside the fixed workspace. -/
theorem final_return_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source finalReturn=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base := by
  have safe:=unused_call "out" (ofString "u256_div") [localVar "out",localVar "den"] (by decide)
  obtain ⟨middle,divisionRun,returnRun⟩:=sequence_returned source post
    (.call (some (some (.local,ofString "out"),none)) (ofString "u256_div") [localVar "out",localVar "den"]) (.return (localVar "out")) returned
    (safe.summary_full source).2.1 normal
  obtain ⟨sum,quotient,sumCell,numeric,canonical,memory⟩:=final_division_normal source middle base context installed den divisionRun
  have out : middle.locals.lookup (ofString "out")=some (RlpWrite.U256Value.tuple quotient):=by
    rw [canonical]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have expected : evaluateHOLFiniteState middle (.return (localVar "out"))=
      (some (.returned (RlpWrite.U256Value.tuple quotient)),emptyLocalsHOLFinite middle):=by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,out,RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have returnedEq : returned=RlpWrite.U256Value.tuple quotient:=by
    have same:=congrArg Prod.fst (returnRun.symm.trans expected)
    cases same
    rfl
  have postEq : post=emptyLocalsHOLFinite middle:=congrArg Prod.snd (returnRun.symm.trans expected)
  have finalFrame : post={middle with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [postEq];rfl
  have combined:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) canonical
  have price:=final_return_cost source base context installed den
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨finalFrame.trans combined,?_,price⟩⟩
  intro query outside
  rw [postEq]
  exact memory query outside

/-- A true returned loop/final suffix derives both its genuine normal
loop exit and its original four-word return from the same parent trace. -/
theorem after_zero_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator))
    (num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator)))
    (den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64)))
    (nz : source.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterZero=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base 449596 := by
  have safe : LocalPrefix (ofString "unused") loop:=.loop loopTest iteration_prefix
  obtain ⟨middle,loopRun,returnRun⟩:=sequence_returned source post loop finalReturn returned (safe.summary_full source).2.1 normal
  obtain ⟨finalIndex,finalAccumulator,finalValues,model,zero⟩:=loop_normal source middle base numerator accumulator context installed acc num den i nz loopRun
  obtain ⟨quotient,returnedEq,result⟩:=final_return_normal middle post base model.context model.installed model.den returned returnRun
  have price:=after_zero_cost source base numerator accumulator context installed acc num den i nz
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨?_,?_,price⟩⟩
  · exact result.state.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}) model.state)
  · intro query outside
    exact (result.away query outside).trans (model.away query outside)

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.final_division_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.final_return_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.after_zero_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad) : Prop where
  context : UDivMod.WideDigits.Workspace.Context source base
  installed : OriginalCode.Installed source.code
  acc : source.locals.lookup (ofString "acc")=some (RlpWrite.U256Value.tuple accumulator)
  num : source.locals.lookup (ofString "num")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad numerator))
  den : source.locals.lookup (ofString "den")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64))

theorem Prepared.withClock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64} {accumulator : Quad}
    (model : Prepared source base numerator accumulator) (clock : Nat) : Prepared {source with clock:=clock} base numerator accumulator :=
  ⟨⟨model.context.global,model.context.domain,model.context.arena,model.context.aligned⟩,model.installed,model.acc,model.num,model.den⟩

theorem Prepared.set {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64} {accumulator : Quad}
    (model : Prepared source base numerator accumulator) (name : MlS) (value : ValueHOL 64)
    (notAcc : name≠ofString "acc") (notNum : name≠ofString "num") (notDen : name≠ofString "den") :
    Prepared (setVarHOLFinite name value source) base numerator accumulator := by
  refine ⟨⟨model.context.global,model.context.domain,model.context.arena,model.context.aligned⟩,model.installed,?_,?_,?_⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notAcc,Ne.symm notAcc] using model.acc
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notNum,Ne.symm notNum] using model.num
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,notDen,Ne.symm notDen] using model.den

def zeroQuad : Quad:=fun _=>0#64
def zeroExpression : ExpHOL 64:=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]
def zeroScope : ProgHOL 64:=.decCall (ofString "nz") .one (ofString "u256_is_zero") [localVar "acc"] afterZero
def initialScopes : ProgHOL 64:=.dec (ofString "out") RlpWrite.U256Value.tupleShape zeroExpression
  (.dec (ofString "i") .one (.const 1#64) (.dec (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression zeroScope))

theorem initial_split : initial=.seq
    (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_mul") [localVar "acc",localVar "den"]) initialScopes := rfl

theorem zero_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) : eval source zeroExpression=some (RlpWrite.U256Value.tuple zeroQuad) := by
  simp [eval,zeroExpression,evalHOLExact,evalListHOLExact,toExact,RlpWrite.U256Value.tuple,zeroQuad]

/-- The original scoped zero test resumes the actual loop/final suffix
with its real flag; clock exhaustion is priced without requiring success. -/
theorem zero_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (model : Prepared source base numerator accumulator)
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64))) :
    source.clock-(evaluateHOLFiniteState source zeroScope).2.clock≤449597 := by
  by_cases funded : 1≤source.clock
  · have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc"]=some [RlpWrite.U256Value.tuple accumulator]:=by
      have acc:=model.acc
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc]
    have actual:=GasBudget.U256Zero.call_execute source accumulator "nz" [localVar "acc"] afterZero args
      (GasBudget.U256Zero.current_code source.code model.installed) funded
    let ready:=bind {source with clock:=source.clock-1} "nz" (GasBudget.U256Zero.resultWord accumulator)
    have next : Prepared ready base numerator accumulator:=(model.withClock (source.clock-1)).set (ofString "nz") (.val (.word (GasBudget.U256Zero.resultWord accumulator))) (by decide) (by decide) (by decide)
    have nextI : ready.locals.lookup (ofString "i")=some (.val (.word 1#64)):=by
      simpa [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
    have nextNz : ready.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator))):=bind_lookup_same _ _ _
    have price:=after_zero_cost ready base numerator accumulator next.context next.installed next.acc next.num next.den nextI nextNz
    have forward:=evaluateHOLFiniteState_clock_le ready afterZero
    have clock : ready.clock=source.clock-1:=rfl
    rw [zeroScope,actual]
    change source.clock-(evaluateHOLFiniteState ready afterZero).2.clock≤449597
    omega
  · omega

/-- The three literal local declarations keep the real accumulator and
constants and introduce the genuine initial counter1before the zero test. -/
theorem initial_scopes_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (model : Prepared source base numerator accumulator) :
    source.clock-(evaluateHOLFiniteState source initialScopes).2.clock≤449597 := by
  let outEntry:=setVarHOLFinite (ofString "out") (RlpWrite.U256Value.tuple zeroQuad) source
  have outModel : Prepared outEntry base numerator accumulator:=model.set (ofString "out") _ (by decide) (by decide) (by decide)
  let indexEntry:=bind outEntry "i" 1#64
  have indexModel : Prepared indexEntry base numerator accumulator:=outModel.set (ofString "i") _ (by decide) (by decide) (by decide)
  let zeroEntry:=setVarHOLFinite (ofString "zero") (RlpWrite.U256Value.tuple zeroQuad) indexEntry
  have zeroModel : Prepared zeroEntry base numerator accumulator:=indexModel.set (ofString "zero") _ (by decide) (by decide) (by decide)
  have index : zeroEntry.locals.lookup (ofString "i")=some (.val (.word 1#64)):=by
    simp [zeroEntry,indexEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
  have zeroPrice:=ClockCost.declared_value_current indexEntry (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression (RlpWrite.U256Value.tuple zeroQuad) zeroScope 449597
    (zero_read indexEntry) (zero_scope_cost zeroEntry base numerator accumulator zeroModel index)
  have indexPrice:=ClockCost.declared_current outEntry "i" (.const 1#64) 1#64 (.dec (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression zeroScope) 449597 rfl zeroPrice
  exact ClockCost.declared_value_current source (ofString "out") RlpWrite.U256Value.tupleShape zeroExpression (RlpWrite.U256Value.tuple zeroQuad)
    (.dec (ofString "i") .one (.const 1#64) (.dec (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression zeroScope)) 449597 (zero_read source) indexPrice

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.Prepared.withClock
#print axioms InitECandidate.Solver.Input.TaylorCurrent.Prepared.set
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_split
#print axioms InitECandidate.Solver.Input.TaylorCurrent.zero_read
#print axioms InitECandidate.Solver.Input.TaylorCurrent.zero_scope_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_scopes_cost

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem initial_product : GasBudget.U256Multiply.productQuad 1#64 11684671#64=GasBudget.U256Multiply.wordQuad 11684671#64 := by
  have product:=denominator_product 1 (by decide)
  change GasBudget.U256Multiply.productQuad 1#64 11684671#64=UDivMod.WideDigits.Single.remainderWords 11684671#64 at product
  exact product.trans (GasBudget.U256Multiply.wordQuad_remainder _).symm

/-- An actual continuing initial multiply derives its exact denominator
accumulator and read-only state at its real two-tick boundary. -/
theorem initial_multiply_ready (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (model : Prepared source base numerator (GasBudget.U256Multiply.wordQuad 1#64))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_mul") [localVar "acc",localVar "den"])=(none,post)) :
    2≤source.clock ∧ Prepared post base numerator (GasBudget.U256Multiply.wordQuad 11684671#64) ∧
      post=setVarHOLFinite (ofString "acc") (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)) {source with clock:=source.clock-2} := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc",localVar "den"]=
      some [RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 1#64),RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)]:=by
    have acc:=model.acc
    have den:=model.den
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc,den]
  obtain ⟨funded,canonical⟩:=GasBudget.U256Multiply.word_assigned_normal source post 1#64 11684671#64 model.installed (ofString "acc") [localVar "acc",localVar "den"] args normal
  rw [initial_product] at canonical
  refine ⟨funded,⟨⟨?_,?_,model.context.arena,model.context.aligned⟩,?_,?_,?_,?_⟩,canonical⟩
  · rw [canonical]
    exact model.context.global
  · rw [canonical]
    exact model.context.domain
  · rw [canonical]
    exact model.installed
  · rw [canonical]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  · rw [canonical]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using model.num
  · rw [canonical]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using model.den

/-- Original initial multiplication and declarations through the whole
loop/final return: only real reached initial states price their suffix. -/
theorem initial_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (model : Prepared source base numerator (GasBudget.U256Multiply.wordQuad 1#64)) :
    source.clock-(evaluateHOLFiniteState source initial).2.clock≤449599 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc",localVar "den"]=
      some [RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 1#64),RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 11684671#64)]:=by
    have acc:=model.acc
    have den:=model.den
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc,den]
  rw [initial_split]
  apply ClockCost.sequence_reached_current source
    (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_mul") [localVar "acc",localVar "den"]) initialScopes 2 449597
    (GasBudget.U256Multiply.word_call_cost source 1#64 11684671#64 model.installed (some (some (ofString "acc"))) [localVar "acc",localVar "den"] args)
  intro middle normal
  obtain ⟨funded,next,canonical⟩:=initial_multiply_ready source middle base numerator model normal
  exact initial_scopes_cost middle base numerator (GasBudget.U256Multiply.wordQuad 11684671#64) next

def tupleEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64) :=
  setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad word)) {source with clock:=source.clock-1}

private theorem from_word_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (price : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word word)])
    (tail : (tupleEntry source name word).clock-(evaluateHOLFiniteState (tupleEntry source name word) continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "u256_from_word") arguments continuation)).2.clock≤price+1 := by
  by_cases funded : 1≤source.clock
  · have actual:=GasBudget.U256Multiply.from_word_call_execute source word installed name arguments continuation args funded
    let ready:=tupleEntry source name word
    change ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price at tail
    have forward:=evaluateHOLFiniteState_clock_le ready continuation
    have clock : ready.clock=source.clock-1:=rfl
    rw [actual]
    change source.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price+1
    omega
  · omega

/-- Actual scalar formals of the original caller, before any startup call. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) : Prop where
  context : UDivMod.WideDigits.Workspace.Context source base
  installed : OriginalCode.Installed source.code
  factor : source.locals.lookup (ofString "factor")=some (.val (.word 1#64))
  numeratorWord : source.locals.lookup (ofString "numerator")=some (.val (.word numerator))
  denominatorWord : source.locals.lookup (ofString "denominator")=some (.val (.word 11684671#64))

theorem Entry.stage {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base numerator : BitVec 64}
    (model : Entry source base numerator) (name : String) (word : BitVec 64) (allowed : name="den" ∨ name="num" ∨ name="acc") :
    Entry (tupleEntry source name word) base numerator := by
  rcases allowed with rfl|rfl|rfl <;>
    refine ⟨⟨model.context.global,model.context.domain,model.context.arena,model.context.aligned⟩,model.installed,?_,?_,?_⟩ <;>
    first
    | simpa [tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using model.factor
    | simpa [tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using model.numeratorWord
    | simpa [tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using model.denominatorWord

/-- Complete unchanged taylor_exponential at its actual blob-price formals:
three from-word calls, initial product, all loop outcomes and final division. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (model : Entry source base numerator) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤449602 := by
  let denEntry:=tupleEntry source "den" 11684671#64
  have denModel : Entry denEntry base numerator:=model.stage "den" _ (Or.inl rfl)
  let numEntry:=tupleEntry denEntry "num" numerator
  have numModel : Entry numEntry base numerator:=denModel.stage "num" _ (Or.inr (Or.inl rfl))
  let accEntry:=tupleEntry numEntry "acc" 1#64
  have accModel : Entry accEntry base numerator:=numModel.stage "acc" _ (Or.inr (Or.inr rfl))
  have prepared : Prepared accEntry base numerator (GasBudget.U256Multiply.wordQuad 1#64):=by
    refine ⟨accModel.context,accModel.installed,?_,?_,?_⟩
    · simp [accEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
    · simp [accEntry,numEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
    · simp [accEntry,numEntry,denEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
  have accArgs : evalListHOLFinite numEntry (h:=fun query=>Classical.propDecidable (numEntry.memaddrs query)) [localVar "factor"]=some [.val (.word 1#64)]:=by
    have factor:=numModel.factor
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,factor]
  have accPrice:=from_word_cost numEntry 1#64 numModel.installed "acc" [localVar "factor"] initial 449599 accArgs (initial_cost accEntry base numerator prepared)
  have numArgs : evalListHOLFinite denEntry (h:=fun query=>Classical.propDecidable (denEntry.memaddrs query)) [localVar "numerator"]=some [.val (.word numerator)]:=by
    have n:=denModel.numeratorWord
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,n]
  have numPrice:=from_word_cost denEntry numerator denModel.installed "num" [localVar "numerator"]
    (.decCall (ofString "acc") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "factor"] initial) 449600 numArgs accPrice
  have denArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "denominator"]=some [.val (.word 11684671#64)]:=by
    have d:=model.denominatorWord
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d]
  rw [body_shape]
  exact from_word_cost source 11684671#64 model.installed "den" [localVar "denominator"]
    (.decCall (ofString "num") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "numerator"]
      (.decCall (ofString "acc") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "factor"] initial)) 449601 denArgs numPrice

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_product
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_multiply_ready
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.Entry.stage
#print axioms InitECandidate.Solver.Input.TaylorCurrent.body_cost

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem from_word_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word word)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "u256_from_word") arguments continuation)=(some (.returned returned),post)) :
    ∃ inner,1≤source.clock ∧ evaluateHOLFiniteState (tupleEntry source name word) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,w⟩:=word_environment source.code.lookup (ofString "u256_from_word") (ofString "w") GasBudget.U256Multiply.fromWordBody
    RlpWrite.U256Value.tupleShape word (GasBudget.U256Multiply.from_word_code source.code installed)
  have funded:=(CallNormal.scoped_returned source post name RlpWrite.U256Value.tupleShape (ofString "u256_from_word") arguments _
    GasBudget.U256Multiply.fromWordBody continuation callee RlpWrite.U256Value.tupleShape args called returned normal).1
  have actual:=GasBudget.U256Multiply.from_word_call_execute source word installed name arguments continuation args funded
  let output:=evaluateHOLFiniteState (tupleEntry source name word) continuation
  have observed : output.1=some (.returned returned):=congrArg Prod.fst (actual.symm.trans normal)
  exact ⟨output.2,funded,Prod.ext observed rfl,congrArg Prod.snd (normal.symm.trans actual)⟩

/-- A real returned zero-test scope derives its own call tick, genuine
initial guard and actual loop/final result, including its NZ restoration. -/
theorem zero_scope_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (model : Prepared source base numerator accumulator)
    (i : source.locals.lookup (ofString "i")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source zeroScope=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base 449597 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "acc"]=some [RlpWrite.U256Value.tuple accumulator]:=by
    have acc:=model.acc
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,acc]
  obtain ⟨callee,called,a⟩:=RlpWrite.U256Value.environment source.code.lookup (ofString "u256_is_zero") GasBudget.U256Zero.body accumulator
    (GasBudget.U256Zero.current_code source.code model.installed)
  have funded:=(CallNormal.scoped_returned source post "nz" .one (ofString "u256_is_zero") [localVar "acc"] _
    GasBudget.U256Zero.body afterZero callee .one args called returned normal).1
  have actual:=GasBudget.U256Zero.call_execute source accumulator "nz" [localVar "acc"] afterZero args
    (GasBudget.U256Zero.current_code source.code model.installed) funded
  let ready:=bind {source with clock:=source.clock-1} "nz" (GasBudget.U256Zero.resultWord accumulator)
  have next : Prepared ready base numerator accumulator:=(model.withClock (source.clock-1)).set (ofString "nz") (.val (.word (GasBudget.U256Zero.resultWord accumulator))) (by decide) (by decide) (by decide)
  have nextI : ready.locals.lookup (ofString "i")=some (.val (.word 1#64)):=by
    simpa [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString] using i
  have nextNz : ready.locals.lookup (ofString "nz")=some (.val (.word (GasBudget.U256Zero.resultWord accumulator))):=bind_lookup_same _ _ _
  let output:=evaluateHOLFiniteState ready afterZero
  have observed : output.1=some (.returned returned):=congrArg Prod.fst (actual.symm.trans normal)
  have run : evaluateHOLFiniteState ready afterZero=(some (.returned returned),output.2):=Prod.ext observed rfl
  obtain ⟨quotient,returnedEq,result⟩:=after_zero_normal ready output.2 base numerator accumulator next.context next.installed next.acc next.num next.den nextI nextNz returned run
  have endpoint : post=restore source "nz" output.2:=congrArg Prod.snd (normal.symm.trans actual)
  have finalFrame : post={output.2 with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [endpoint];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  change {output.2 with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have price:=zero_scope_cost source base numerator accumulator model i
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨finalFrame.trans projected,?_,price⟩⟩
  intro query outside
  rw [endpoint]
  exact result.away query outside

/-- Real returned startup declarations expose their actual inner scopes
and restore OUT/I/ZERO around the same returned loop result. -/
theorem initial_scopes_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (accumulator : Quad)
    (model : Prepared source base numerator accumulator)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source initialScopes=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base 449597 := by
  obtain ⟨outValue,outInner,outRead,outValid,outRun,outRestored⟩:=CallNormal.declaration_normal_entry source post "out" RlpWrite.U256Value.tupleShape zeroExpression
    (.dec (ofString "i") .one (.const 1#64) (.dec (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression zeroScope)) returned normal
  have outEq : outValue=RlpWrite.U256Value.tuple zeroQuad:=Option.some.inj (outRead.symm.trans (zero_read source))
  subst outValue
  let outEntry:=setVarHOLFinite (ofString "out") (RlpWrite.U256Value.tuple zeroQuad) source
  have outModel : Prepared outEntry base numerator accumulator:=model.set (ofString "out") _ (by decide) (by decide) (by decide)
  obtain ⟨indexInner,indexRun,indexRestored⟩:=ScalarScope.declare_trace outEntry outInner "i" (.const 1#64) 1#64
    (.dec (ofString "zero") RlpWrite.U256Value.tupleShape zeroExpression zeroScope) (some (.returned returned)) rfl outRun
  let indexEntry:=bind outEntry "i" 1#64
  have indexModel : Prepared indexEntry base numerator accumulator:=outModel.set (ofString "i") _ (by decide) (by decide) (by decide)
  obtain ⟨zeroValue,zeroInner,zeroRead,zeroValid,zeroRun,zeroRestored⟩:=CallNormal.declaration_normal_entry indexEntry indexInner "zero" RlpWrite.U256Value.tupleShape zeroExpression zeroScope returned indexRun
  have zeroEq : zeroValue=RlpWrite.U256Value.tuple zeroQuad:=Option.some.inj (zeroRead.symm.trans (zero_read indexEntry))
  subst zeroValue
  let zeroEntry:=setVarHOLFinite (ofString "zero") (RlpWrite.U256Value.tuple zeroQuad) indexEntry
  have zeroModel : Prepared zeroEntry base numerator accumulator:=indexModel.set (ofString "zero") _ (by decide) (by decide) (by decide)
  have index : zeroEntry.locals.lookup (ofString "i")=some (.val (.word 1#64)):=by
    simp [zeroEntry,indexEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
  obtain ⟨quotient,returnedEq,result⟩:=zero_scope_normal zeroEntry zeroInner base numerator accumulator zeroModel index returned zeroRun
  have finalFrame : post={zeroInner with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [outRestored,indexRestored,zeroRestored];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  change {zeroInner with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have price:=initial_scopes_cost source base numerator accumulator model
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨finalFrame.trans projected,?_,price⟩⟩
  intro query outside
  rw [outRestored,indexRestored,zeroRestored]
  exact result.away query outside

/-- A genuine returned initial product/scope prefix supplies the same
full actual function result without a future normal-call premise. -/
theorem initial_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (model : Prepared source base numerator (GasBudget.U256Multiply.wordQuad 1#64))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source initial=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base 449599 := by
  have safe:=unused_call "acc" (ofString "u256_mul") [localVar "acc",localVar "den"] (by decide)
  have modeled : evaluateHOLFiniteState source (.seq
      (.call (some (some (.local,ofString "acc"),none)) (ofString "u256_mul") [localVar "acc",localVar "den"]) initialScopes)=(some (.returned returned),post):=by
    rw [←initial_split]
    exact normal
  obtain ⟨middle,multiplyRun,scopesRun⟩:=sequence_returned source post _ _ returned (safe.summary_full source).2.1 modeled
  obtain ⟨funded,next,canonical⟩:=initial_multiply_ready source middle base numerator model multiplyRun
  obtain ⟨quotient,returnedEq,result⟩:=initial_scopes_normal middle post base numerator (GasBudget.U256Multiply.wordQuad 11684671#64) next returned scopesRun
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) canonical
  have price:=initial_cost source base numerator model
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨result.state.trans projected,?_,price⟩⟩
  intro query outside
  have memory : middle.memory=source.memory:=by rw [canonical];rfl
  exact (result.away query outside).trans (congrFun memory query)

/-- The actual returned complete Taylor body derives its real startup,
normal loop/final return and all lexical restorations. Its true returned quad
and protected physical memory belong to that same execution. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64) (model : Entry source base numerator)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ WorkspaceResult source post base 449602 := by
  let denEntry:=tupleEntry source "den" 11684671#64
  have denModel : Entry denEntry base numerator:=model.stage "den" _ (Or.inl rfl)
  let numEntry:=tupleEntry denEntry "num" numerator
  have numModel : Entry numEntry base numerator:=denModel.stage "num" _ (Or.inr (Or.inl rfl))
  let accEntry:=tupleEntry numEntry "acc" 1#64
  have accModel : Entry accEntry base numerator:=numModel.stage "acc" _ (Or.inr (Or.inr rfl))
  have denArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "denominator"]=some [.val (.word 11684671#64)]:=by
    have d:=model.denominatorWord
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d]
  have modeled:=normal
  rw [body_shape] at modeled
  obtain ⟨denInner,denFunded,denRun,denRestored⟩:=from_word_returned source post 11684671#64 model.installed "den" [localVar "denominator"]
    (.decCall (ofString "num") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "numerator"]
      (.decCall (ofString "acc") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "factor"] initial)) denArgs returned modeled
  have numArgs : evalListHOLFinite denEntry (h:=fun query=>Classical.propDecidable (denEntry.memaddrs query)) [localVar "numerator"]=some [.val (.word numerator)]:=by
    have n:=denModel.numeratorWord
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,n]
  obtain ⟨numInner,numFunded,numRun,numRestored⟩:=from_word_returned denEntry denInner numerator denModel.installed "num" [localVar "numerator"]
    (.decCall (ofString "acc") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "factor"] initial) numArgs returned denRun
  have accArgs : evalListHOLFinite numEntry (h:=fun query=>Classical.propDecidable (numEntry.memaddrs query)) [localVar "factor"]=some [.val (.word 1#64)]:=by
    have f:=numModel.factor
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,f]
  obtain ⟨accInner,accFunded,accRun,accRestored⟩:=from_word_returned numEntry numInner 1#64 numModel.installed "acc" [localVar "factor"] initial accArgs returned numRun
  have prepared : Prepared accEntry base numerator (GasBudget.U256Multiply.wordQuad 1#64):=by
    refine ⟨accModel.context,accModel.installed,?_,?_,?_⟩
    · simp [accEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
    · simp [accEntry,numEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
    · simp [accEntry,numEntry,denEntry,tupleEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE,ofString]
  obtain ⟨quotient,returnedEq,result⟩:=initial_normal accEntry accInner base numerator prepared returned accRun
  have finalFrame : post={accInner with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [denRestored,numRestored,accRestored];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  change {accInner with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have price:=body_cost source base numerator model
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨finalFrame.trans projected,?_,price⟩⟩
  intro query outside
  rw [denRestored,numRestored,accRestored]
  exact result.away query outside

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.zero_scope_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_scopes_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.initial_normal
#print axioms InitECandidate.Solver.Input.TaylorCurrent.body_normal

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "taylor_exponential")=some
      ([(ofString "factor",.one),(ofString "numerator",.one),(ofString "denominator",.one)],body,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 213
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_taylor_exponential) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_taylor_exponential,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def values (numerator : BitVec 64) : List (ValueHOL 64):=
  [.val (.word 1#64),.val (.word numerator),.val (.word 11684671#64)]

theorem environment (codeFn : MlS→ Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (numerator : BitVec 64)
    (code : codeFn (ofString "taylor_exponential")=some
      ([(ofString "factor",.one),(ofString "numerator",.one),(ofString "denominator",.one)],body,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "taylor_exponential") (values numerator)=some (body,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "factor")=some (.val (.word 1#64)) ∧
      callee.lookup (ofString "numerator")=some (.val (.word numerator)) ∧
      callee.lookup (ofString "denominator")=some (.val (.word 11684671#64)) :=
  word_triple_environment codeFn (ofString "taylor_exponential") (ofString "factor") (ofString "numerator") (ofString "denominator")
    body RlpWrite.U256Value.tupleShape 1#64 numerator 11684671#64 (by decide) (by decide) (by decide) code

private theorem callee_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (factor : callee.lookup (ofString "factor")=some (.val (.word 1#64)))
    (num : callee.lookup (ofString "numerator")=some (.val (.word numerator)))
    (den : callee.lookup (ofString "denominator")=some (.val (.word 11684671#64))) :
    Entry (callEntryStateHOLFinite source callee) base numerator :=
  ⟨⟨context.global,context.domain,context.arena,context.aligned⟩,installed,factor,num,den⟩

/-- All original call forms use the real three-word ABI and body allowance.
No child return or lower bound on the incoming clock is required. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values numerator)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "taylor_exponential") arguments)).2.clock≤449603 := by
  obtain ⟨callee,called,factor,num,den⟩:=environment source.code.lookup numerator (original_code source.code installed)
  exact ClockCost.call_current source destination (ofString "taylor_exponential") arguments _ body callee RlpWrite.U256Value.tupleShape 449602
    args called (body_cost (callEntryStateHOLFinite source callee) base numerator (callee_entry source base numerator context installed callee factor num den))

/-- A genuine returned child supplies its actual quad and caller frame at
the child's real remaining clock, without assuming worst-case funding. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code) (name : String)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "taylor_exponential") (values numerator)=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧
      WorkspaceResult (callEntryStateHOLFinite source callee) target base 449602 ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple quotient)
          {source with memory:=target.memory,clock:=target.clock} := by
  obtain ⟨expected,lookup,factor,num,den⟩:=environment source.code.lookup numerator (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at factor num den
  rw [bodyEq] at run
  obtain ⟨quotient,returnedEq,result⟩:=body_normal (callEntryStateHOLFinite source callee) target base numerator
    (callee_entry source base numerator context installed callee factor num den) returned run
  refine ⟨quotient,returnedEq,result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=target.clock} at frame
  rw [CallNormal.continuationEntry,returnedEq,frame]

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.original_code
#print axioms InitECandidate.Solver.Input.TaylorCurrent.environment
#print axioms InitECandidate.Solver.Input.TaylorCurrent.call_cost
#print axioms InitECandidate.Solver.Input.TaylorCurrent.resume

namespace InitECandidate.Solver.Input.BlobPriceCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_calculate_blob_gas_price with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64):=[.const 1#64,localVar "excess_blob_gas",.const 11684671#64]

theorem body_shape : body=.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "taylor_exponential") arguments (.return (localVar "r")) := by
  simp [body,Guest.Software.guestFn_calculate_blob_gas_price,progToHOL,expToHOL,shapeToHOL,arguments,localVar,RlpWrite.U256Value.tupleShape]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "calculate_blob_gas_price")=some ([(ofString "excess_blob_gas",.one)],body,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 214
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_calculate_blob_gas_price) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_calculate_blob_gas_price,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- The literal blob-price wrapper adds only its Taylor call tick;
returning the real scoped quad spends no source clock. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (excess : source.locals.lookup (ofString "excess_blob_gas")=some (.val (.word numerator))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤449603 := by
  obtain ⟨callee,called,factor,num,den⟩:=TaylorCurrent.environment source.code.lookup numerator (TaylorCurrent.original_code source.code installed)
  have entry : TaylorCurrent.Entry (callEntryStateHOLFinite source callee) base numerator:=
    ⟨⟨context.global,context.domain,context.arena,context.aligned⟩,installed,factor,num,den⟩
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (TaylorCurrent.values numerator):=by
    simp [arguments,TaylorCurrent.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,excess]
  rw [body_shape]
  exact ClockCost.scoped_reached_current source "r" RlpWrite.U256Value.tupleShape (ofString "taylor_exponential") arguments _
    TaylorCurrent.body (.return (localVar "r")) callee RlpWrite.U256Value.tupleShape 449602 0 args called
    (TaylorCurrent.body_cost (callEntryStateHOLFinite source callee) base numerator entry)
    (by
      intro target returned run valid
      change (CallNormal.continuationEntry source target "r" returned).clock-
        (evaluateHOLFiniteState (CallNormal.continuationEntry source target "r" returned) (.return (localVar "r"))).2.clock≤0
      exact ClockCost.returned _ _ (CallNormal.continuationEntry source target "r" returned) rfl)

/-- A real wrapper return exposes the same Taylor quad and protected memory,
including the wrapper's actual scoped continuation and lexical restoration. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (excess : source.locals.lookup (ofString "excess_blob_gas")=some (.val (.word numerator)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ TaylorCurrent.WorkspaceResult source post base 449603 := by
  obtain ⟨callee,called,factor,num,den⟩:=TaylorCurrent.environment source.code.lookup numerator (TaylorCurrent.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (TaylorCurrent.values numerator):=by
    simp [arguments,TaylorCurrent.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,excess]
  have modeled:=normal
  rw [body_shape] at modeled
  obtain ⟨funded,target,child,inner,childRun,valid,returnRun,restored⟩:=CallNormal.scoped_returned source post "r"
    RlpWrite.U256Value.tupleShape (ofString "taylor_exponential") arguments _ TaylorCurrent.body (.return (localVar "r"))
    callee RlpWrite.U256Value.tupleShape args called returned modeled
  obtain ⟨quotient,childEq,result,entryEq⟩:=TaylorCurrent.resume source target base numerator context installed "r"
    TaylorCurrent.body callee RlpWrite.U256Value.tupleShape called child childRun
  let ready:=CallNormal.continuationEntry source target "r" child
  have cell : ready.locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple quotient):=by
    change (CallNormal.continuationEntry source target "r" child).locals.lookup (ofString "r")=some (RlpWrite.U256Value.tuple quotient)
    rw [entryEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update_pointwise,FUPDATE]
  have expected : evaluateHOLFiniteState ready (.return (localVar "r"))=
      (some (.returned (RlpWrite.U256Value.tuple quotient)),emptyLocalsHOLFinite ready):=by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,cell,RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have returnedEq : returned=RlpWrite.U256Value.tuple quotient:=by
    have same:=congrArg Prod.fst (returnRun.symm.trans expected)
    cases same
    rfl
  have innerEq : inner=emptyLocalsHOLFinite ready:=congrArg Prod.snd (returnRun.symm.trans expected)
  have finalFrame : post={target with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [restored,innerEq];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  change {target with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  have price:=body_cost source base numerator context installed excess
  rw [normal] at price
  refine ⟨quotient,returnedEq,⟨finalFrame.trans projected,?_,price⟩⟩
  intro query outside
  rw [restored,innerEq]
  exact result.away query outside

/-- The original one-word caller adds one call tick to the wrapper. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word numerator)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "calculate_blob_gas_price") expressions)).2.clock≤449604 := by
  obtain ⟨callee,called,excess⟩:=word_environment source.code.lookup (ofString "calculate_blob_gas_price") (ofString "excess_blob_gas")
    body RlpWrite.U256Value.tupleShape numerator (original_code source.code installed)
  have entry : UDivMod.WideDigits.Workspace.Context (callEntryStateHOLFinite source callee) base:=
    ⟨context.global,context.domain,context.arena,context.aligned⟩
  exact ClockCost.call_current source destination (ofString "calculate_blob_gas_price") expressions _ body callee RlpWrite.U256Value.tupleShape
    449603 args called (body_cost (callEntryStateHOLFinite source callee) base numerator entry installed excess)

/-- The caller receives the real returned quad and full outside-workspace
frame at the actual remaining clock of this wrapper execution. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base numerator : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code) (name : String)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "calculate_blob_gas_price") [.val (.word numerator)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧
      TaylorCurrent.WorkspaceResult (callEntryStateHOLFinite source callee) target base 449603 ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple quotient)
          {source with memory:=target.memory,clock:=target.clock} := by
  obtain ⟨expected,lookup,excess⟩:=word_environment source.code.lookup (ofString "calculate_blob_gas_price") (ofString "excess_blob_gas")
    body RlpWrite.U256Value.tupleShape numerator (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at excess
  rw [bodyEq] at run
  have entry : UDivMod.WideDigits.Workspace.Context (callEntryStateHOLFinite source callee) base:=
    ⟨context.global,context.domain,context.arena,context.aligned⟩
  obtain ⟨quotient,returnedEq,result⟩:=body_normal (callEntryStateHOLFinite source callee) target base numerator entry installed excess returned run
  refine ⟨quotient,returnedEq,result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=target.clock} at frame
  rw [CallNormal.continuationEntry,returnedEq,frame]

end InitECandidate.Solver.Input.BlobPriceCurrent

#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.body_shape
#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.original_code
#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.body_cost
#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.body_normal
#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.call_cost
#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.resume

namespace InitECandidate.Solver.Input.BlobPriceCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Arbitrary one-expression scoped callers either fail their actual read
or ABI check, or enter the checked wrapper at its real scalar argument. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tail : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape
      (ofString "calculate_blob_gas_price") [expression] continuation)).2.clock≤449604+tailPrice := by
  classical
  cases read : eval source expression with
  | none=>
    simp only [eval] at read
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp [evalListHOLFinite,evalListHOLExact,read]
  | some value=>
    let actualValues : List (ValueHOL 64):=[value]
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [expression]=some actualValues:=by
      simp only [eval] at read
      simp [actualValues,evalListHOLFinite,evalListHOLExact,read]
    cases value with
    | val payload=>
      cases payload with
      | word numerator=>
        obtain ⟨callee,called,excess⟩:=word_environment source.code.lookup (ofString "calculate_blob_gas_price") (ofString "excess_blob_gas")
          body RlpWrite.U256Value.tupleShape numerator (original_code source.code installed)
        have entry : UDivMod.WideDigits.Workspace.Context (callEntryStateHOLFinite source callee) base:=
          ⟨context.global,context.domain,context.arena,context.aligned⟩
        have price:=ClockCost.scoped_current source (ofString name) RlpWrite.U256Value.tupleShape (ofString "calculate_blob_gas_price")
          [expression] _ body continuation callee RlpWrite.U256Value.tupleShape 449603 tailPrice args called
          (body_cost (callEntryStateHOLFinite source callee) base numerator entry installed excess) tail
        omega
    | rStruct fields | nStruct constructor fields=>
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "calculate_blob_gas_price") actualValues=none:=by
        apply (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr
        unfold lookupCodeHOLExact
        rw [original_code source.code installed]
        simp [actualValues,shapeOfHOLExact,shapeEqHOL]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
      simp [failed]

end InitECandidate.Solver.Input.BlobPriceCurrent

#print axioms InitECandidate.Solver.Input.BlobPriceCurrent.scoped_cost

namespace InitECandidate.Solver.Input.ExcessBlobCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_calculate_excess_blob_gas with | .function fn=>progToHOL fn.body | _=>.skip
def field (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "parent",.const (BitVec.ofNat 64 offset)])
def baseFee : ExpHOL 64:=.load RlpWrite.U256Value.tupleShape (.op .add [localVar "parent",.const 160#64])
def quotientArgument : ExpHOL 64:=.panop .mul [localVar "used",.op .sub [.const 21#64,.const 14#64]]
def quotientReturn : ProgHOL 64:=.return (.op .add [localVar "excess",localVar "q"])
def quotientCall : ProgHOL 64:=.decCall (ofString "q") .one (ofString "udiv") [quotientArgument,.const 21#64] quotientReturn
def finish : ProgHOL 64:=.seq
  (.ite (.cmp .notEqual (localVar "gt") (.const 0#64)) quotientCall .skip)
  (.return (.op .sub [localVar "parent_blob_gas",.const 1835008#64]))
def afterPrice : ProgHOL 64:=
  .decCall (ofString "per_blob") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [.const 131072#64]
  (.decCall (ofString "target_price") RlpWrite.U256Value.tupleShape (ofString "u256_mul") [localVar "per_blob",localVar "price"]
  (.decCall (ofString "base_cost") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [.const 8192#64]
  (.decCall (ofString "base_blob_tx_price") RlpWrite.U256Value.tupleShape (ofString "u256_mul") [localVar "base_cost",localVar "base_fee"]
  (.decCall (ofString "gt") .one (ofString "u256_gt") [localVar "base_blob_tx_price",localVar "target_price"] finish))))
def priceCall : ProgHOL 64:=.decCall (ofString "price") RlpWrite.U256Value.tupleShape (ofString "calculate_blob_gas_price") [localVar "excess"] afterPrice
def afterParent : ProgHOL 64:=.seq
  (.ite (.cmp .lower (localVar "parent_blob_gas") (.const 1835008#64)) (.return (.const 0#64)) .skip) priceCall

theorem body_shape : body=
    .dec (ofString "excess") .one (field 208)
    (.dec (ofString "used") .one (field 200)
    (.dec (ofString "base_fee") RlpWrite.U256Value.tupleShape baseFee
    (.dec (ofString "parent_blob_gas") .one (.op .add [localVar "excess",localVar "used"]) afterParent))) := by
  simp [body,Guest.Software.guestFn_calculate_excess_blob_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    field,baseFee,afterParent,priceCall,afterPrice,finish,quotientCall,quotientArgument,quotientReturn,localVar,RlpWrite.U256Value.tupleShape]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "calculate_excess_blob_gas")=some ([(ofString "parent",.one)],body,.one) := by
  have checked:=OriginalCode.indexed code installed 215
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_calculate_excess_blob_gas) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_calculate_excess_blob_gas,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- The real final scalar division has a fixed nonzero divisor. Its
64-round software body and both call ticks cover every failed/short path. -/
theorem quotient_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code quotientCall 66 := by
  intro source sameCode
  apply ClockCost.word_pair_const source (ofString "udiv") (ofString "a") (ofString "b") (ofString "q")
    UDivMod.Divide.body quotientReturn .one .one quotientArgument 21#64 65 0 (by decide)
  · rw [sameCode]
    exact UDivMod.Divide.original_code code installed
  · intro entry left same a b
    apply UDivMod.Divide.nonzero_cost entry left 21#64 a b (by decide)
    rw [same,sameCode]
    exact UDivMod.original_code code installed
  · exact ClockCost.returned source.code _

/-- The unchanged post-price arithmetic has no input-dependent source
loop except the already bounded nonzero scalar division. -/
theorem after_price_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterPrice 86 := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  have tail : ClockCost.Bound code finish 66:=by
    unfold finish
    exact ClockCost.sequence code _ _ 66 0
      (ClockCost.conditional code _ _ _ 66 0 (quotient_cost code installed) (ClockCost.skip code)) (ClockCost.returned code _)
  unfold afterPrice
  refine ClockCost.scoped_body code _ _ _ _ _ _ _ _ 0 85 (environment .u256_from_word)
    (GasBudget.ArithmeticEffects.price_u256_from_word code environment) ?_
  refine ClockCost.scoped_body code _ _ _ _ _ _ _ _ 7 77 (environment .u256_mul)
    (GasBudget.ArithmeticEffects.price_u256_mul code environment) ?_
  refine ClockCost.scoped_body code _ _ _ _ _ _ _ _ 0 76 (environment .u256_from_word)
    (GasBudget.ArithmeticEffects.price_u256_from_word code environment) ?_
  refine ClockCost.scoped_body code _ _ _ _ _ _ _ _ 7 68 (environment .u256_mul)
    (GasBudget.ArithmeticEffects.price_u256_mul code environment) ?_
  exact ClockCost.scoped_body code _ _ _ _ _ _ _ _ 1 66 (environment .u256_gt)
    (GasBudget.ArithmeticEffects.price_u256_gt code environment) tail

theorem after_parent_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterParent).2.clock≤449690 := by
  unfold afterParent
  apply ClockCost.stopping_guard_current source _ (.return (.const 0#64)) priceCall 0 449690
  · simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  · exact ClockCost.returned _ _ source rfl
  · exact BlobPriceCurrent.scoped_cost source base context installed "price" (localVar "excess") afterPrice 86
      (after_price_cost source.code installed)

/-- The original helper's actual declarations preserve the workspace.
Every read/shape failure and early returned branch is included. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤449690 := by
  rw [body_shape]
  apply ClockCost.declared_reached_current
  intro excess excessRead excessShape
  apply ClockCost.declared_reached_current
  intro used usedRead usedShape
  apply ClockCost.declared_reached_current
  intro fee feeRead feeShape
  apply ClockCost.declared_reached_current
  intro parent parentRead parentShape
  exact after_parent_cost _ base ⟨context.global,context.domain,context.arena,context.aligned⟩ installed

end InitECandidate.Solver.Input.ExcessBlobCurrent

#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.body_shape
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.original_code
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.quotient_cost
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.after_price_cost
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.after_parent_cost
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.body_cost

namespace InitECandidate.Solver.Input.ExcessBlobCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Price every original call form directly at its current workspace.
The helper needs no assumed successful parent-header loads. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "calculate_excess_blob_gas") arguments)).2.clock≤449691 := by
  apply ClockCost.call_arguments_current source destination (ofString "calculate_excess_blob_gas") arguments 449690
  intro values actual callee shape args called
  have same:=LocalEffects.lookup_body source.code (ofString "calculate_excess_blob_gas") [(ofString "parent",.one)] body .one
    (original_code source.code installed) values actual callee shape called
  rw [same]
  exact body_cost (callEntryStateHOLFinite source callee) base ⟨context.global,context.domain,context.arena,context.aligned⟩ installed

/-- A scoped original header caller adds its own tick and an independently
checked continuation. Actual callee entries retain the caller workspace. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tail : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "calculate_excess_blob_gas") arguments continuation)).2.clock≤449691+tailPrice := by
  have priced : ∀ values actual callee shape,
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values →
      lookupCodeHOLFinite source.code.lookup (ofString "calculate_excess_blob_gas") values=some (actual,callee,shape) →
      (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual).2.clock≤449690:=by
    intro values actual callee shape args called
    have same:=LocalEffects.lookup_body source.code (ofString "calculate_excess_blob_gas") [(ofString "parent",.one)] body .one
      (original_code source.code installed) values actual callee shape called
    rw [same]
    exact body_cost (callEntryStateHOLFinite source callee) base ⟨context.global,context.domain,context.arena,context.aligned⟩ installed
  have price:=ClockCost.scoped_arguments_current source name .one (ofString "calculate_excess_blob_gas") arguments continuation
    449690 tailPrice priced tail
  omega

end InitECandidate.Solver.Input.ExcessBlobCurrent

#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.call_cost
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.scoped_cost

namespace InitECandidate.Solver.Input.ExcessBlobCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The literal scalar division has divisor 21 even when its first read
fails. Every reached child therefore preserves the full nonlocal state. -/
theorem quotient_frame (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code quotientCall := by
  intro source sameCode
  rw [quotientCall]
  apply LocalEffects.word_pair_const source (ofString "udiv") (ofString "a") (ofString "b") (ofString "q")
    UDivMod.Divide.body quotientReturn .one .one quotientArgument 21#64 (by decide)
    (UDivMod.Divide.original_code source.code (sameCode.symm ▸ installed))
  · intro entry left codeEq a b
    exact UDivMod.Divide.nonzero_frame entry left 21#64 a b (by decide)
      (UDivMod.original_code entry.code (by rw [codeEq,sameCode];exact installed))
  · exact LocalEffects.returned source.code _

/-- After the real blob-price call, the unchanged arithmetic and nonzero
scalar division preserve every memory cell, global and other nonlocal field. -/
theorem after_price_frame (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code afterPrice := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  have tail : LocalEffects.Preserves code finish:=by
    unfold finish
    exact LocalEffects.sequence code _ _
      (LocalEffects.conditional code _ _ _ (quotient_frame code installed) (LocalEffects.skip code)) (LocalEffects.returned code _)
  unfold afterPrice
  refine LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_from_word)
    (GasBudget.ArithmeticEffects.original_preserves .u256_from_word code environment) ?_
  refine LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_mul)
    (GasBudget.ArithmeticEffects.original_preserves .u256_mul code environment) ?_
  refine LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_from_word)
    (GasBudget.ArithmeticEffects.original_preserves .u256_from_word code environment) ?_
  refine LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_mul)
    (GasBudget.ArithmeticEffects.original_preserves .u256_mul code environment) ?_
  exact LocalEffects.scoped_body code _ _ _ _ _ _ _ _ (environment .u256_gt)
    (GasBudget.ArithmeticEffects.original_preserves .u256_gt code environment) tail

end InitECandidate.Solver.Input.ExcessBlobCurrent

#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.quotient_frame
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.after_price_frame

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem WorkspaceResult.of_erase {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {price : Nat}
    (frame : LocalEffects.erase post=LocalEffects.erase source) (cost : source.clock-post.clock≤price) :
    WorkspaceResult source post base price := by
  refine ⟨?_,?_,cost⟩
  · have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}) frame
    exact projected
  · intro query outside
    exact congrFun (LocalEffects.memory_of_erase source post frame) query

end InitECandidate.Solver.Input.TaylorCurrent

namespace InitECandidate.Solver.Input.ExcessBlobCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual returned price scope preserves the caller's protected
memory through its genuine arithmetic continuation and lexical restoration. -/
theorem price_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source priceCall=(some (.returned returned),post)) :
    TaylorCurrent.WorkspaceResult source post base 449690 := by
  classical
  cases read : eval source (localVar "excess") with
  | none=>
    simp only [eval] at read
    rw [priceCall,evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
    simp [evalListHOLFinite,evalListHOLExact,read] at normal
  | some value=>
    let actualValues : List (ValueHOL 64):=[value]
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "excess"]=some actualValues:=by
      simp only [eval] at read
      simp [actualValues,evalListHOLFinite,evalListHOLExact,read]
    cases value with
    | val payload=>
      cases payload with
      | word numerator=>
        obtain ⟨callee,called,excess⟩:=word_environment source.code.lookup (ofString "calculate_blob_gas_price") (ofString "excess_blob_gas")
          BlobPriceCurrent.body RlpWrite.U256Value.tupleShape numerator (BlobPriceCurrent.original_code source.code installed)
        obtain ⟨funded,target,child,inner,childRun,valid,tailRun,restored⟩:=CallNormal.scoped_returned source post "price"
          RlpWrite.U256Value.tupleShape (ofString "calculate_blob_gas_price") [localVar "excess"] _ BlobPriceCurrent.body afterPrice
          callee RlpWrite.U256Value.tupleShape args called returned normal
        obtain ⟨quotient,childEq,result,entryEq⟩:=BlobPriceCurrent.resume source target base numerator context installed "price"
          BlobPriceCurrent.body callee RlpWrite.U256Value.tupleShape called child childRun
        let ready:=CallNormal.continuationEntry source target "price" child
        have code : ready.code=source.code:=by
          change (CallNormal.continuationEntry source target "price" child).code=source.code
          rw [entryEq]
          rfl
        have unchanged:=after_price_frame source.code installed ready code
        rw [tailRun] at unchanged
        have finalFrame : post={inner with
            locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [restored];rfl
        have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
          locals:=post.locals,memory:=post.memory,clock:=post.clock}) unchanged
        change {inner with locals:=post.locals,memory:=post.memory,clock:=post.clock}={ready with
          locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
        have original : {ready with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
            locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by
          change {CallNormal.continuationEntry source target "price" child with
            locals:=post.locals,memory:=post.memory,clock:=post.clock}=_
          rw [entryEq]
          rfl
        have price:=BlobPriceCurrent.scoped_cost source base context installed "price" (localVar "excess") afterPrice 86
          (after_price_cost source.code installed)
        change source.clock-(evaluateHOLFiniteState source priceCall).2.clock≤449690 at price
        rw [normal] at price
        refine ⟨finalFrame.trans (projected.trans original),?_,price⟩
        intro query outside
        rw [restored]
        exact (congrFun (LocalEffects.memory_of_erase ready inner unchanged) query).trans (result.away query outside)
    | rStruct fields | nStruct constructor fields=>
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "calculate_blob_gas_price") actualValues=none:=by
        apply (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr
        unfold lookupCodeHOLExact
        rw [BlobPriceCurrent.original_code source.code installed]
        simp [actualValues,shapeOfHOLExact,shapeEqHOL]
      rw [priceCall,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at normal
      simp only [failed] at normal
      cases normal

/-- The actual early-return decision either finishes without touching
memory or reaches the real price scope at the identical current state. -/
theorem after_parent_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterParent=(some (.returned returned),post)) :
    TaylorCurrent.WorkspaceResult source post base 449690 := by
  let guard : ProgHOL 64:=.ite (.cmp .lower (localVar "parent_blob_gas") (.const 1835008#64)) (.return (.const 0#64)) .skip
  have decision : PureDecision guard:=.ite _ (.returned _) .skip
  have unchanged:=decision.summary source
  have pureFrame : LocalEffects.Preserves source.code guard:=
    LocalEffects.conditional source.code (.cmp .lower (localVar "parent_blob_gas") (.const 1835008#64)) _ _
      (LocalEffects.returned source.code (.const 0#64)) (LocalEffects.skip source.code)
  have frame:=pureFrame source rfl
  have price:=after_parent_cost source base context installed
  rw [normal] at price
  change evaluateHOLFiniteState source (.seq guard priceCall)=(some (.returned returned),post) at normal
  rw [evaluateHOLFiniteState_seq_line780] at normal
  generalize observed : evaluateHOLFiniteState source guard=output at unchanged frame normal
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>
    have same : middle=source:=unchanged.1 rfl
    subst middle
    exact price_call_normal source post base context installed returned normal
  | some result=>
    have endpoint : middle=post:=congrArg Prod.snd normal
    rw [endpoint] at frame
    exact TaylorCurrent.WorkspaceResult.of_erase frame price

private theorem declared_result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) (continuation : ProgHOL 64) (price : Nat) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.dec (ofString name) shape expression continuation)=(some (.returned returned),post))
    (reached : ∀ declared inner,eval source expression=some declared → shapeEqHOL shape (shapeOfHOLExact declared)=true →
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation=(some (.returned returned),inner) →
      TaylorCurrent.WorkspaceResult (setVarHOLFinite (ofString name) declared source) inner base price) :
    TaylorCurrent.WorkspaceResult source post base price := by
  obtain ⟨declared,inner,read,typed,run,restored⟩:=CallNormal.declaration_normal_entry source post name shape expression continuation returned normal
  have result:=reached declared inner read typed run
  have finalFrame : post={inner with
      locals:=post.locals,memory:=post.memory,clock:=post.clock}:=by rw [restored];rfl
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
  change {inner with locals:=post.locals,memory:=post.memory,clock:=post.clock}={source with
    locals:=post.locals,memory:=post.memory,clock:=post.clock} at projected
  refine ⟨finalFrame.trans projected,?_,?_⟩
  · intro query outside
    rw [restored]
    exact result.away query outside
  · rw [restored]
    exact result.cost

/-- A genuine original helper return derives all four real declaration
entries, its selected branch and the complete outside-workspace memory frame. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    TaylorCurrent.WorkspaceResult source post base 449690 := by
  rw [body_shape] at normal
  apply declared_result source post base "excess" .one (field 208) _ 449690 returned normal
  intro excess excessInner excessRead excessShape excessRun
  apply declared_result _ excessInner base "used" .one (field 200) _ 449690 returned excessRun
  intro used usedInner usedRead usedShape usedRun
  apply declared_result _ usedInner base "base_fee" RlpWrite.U256Value.tupleShape baseFee _ 449690 returned usedRun
  intro fee feeInner feeRead feeShape feeRun
  apply declared_result _ feeInner base "parent_blob_gas" .one (.op .add [localVar "excess",localVar "used"]) _ 449690 returned feeRun
  intro parent parentInner parentRead parentShape parentRun
  exact after_parent_normal _ parentInner base ⟨context.global,context.domain,context.arena,context.aligned⟩ installed returned parentRun

end InitECandidate.Solver.Input.ExcessBlobCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.WorkspaceResult.of_erase
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.price_call_normal
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.after_parent_normal
#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.body_normal_frame

namespace InitECandidate.Solver.Input.ExcessBlobCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal child returns retain the original header caller's
metadata and protected memory at that child's real remaining clock. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (name : String) (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "calculate_excess_blob_gas") values=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    TaylorCurrent.WorkspaceResult (callEntryStateHOLFinite source callee) target base 449690 ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) returned {source with memory:=target.memory,clock:=target.clock} := by
  have bodyEq:=LocalEffects.lookup_body source.code (ofString "calculate_excess_blob_gas") [(ofString "parent",.one)] body .one
    (original_code source.code installed) values actual callee shape called
  rw [bodyEq] at run
  have result:=body_normal_frame (callEntryStateHOLFinite source callee) target base
    ⟨context.global,context.domain,context.arena,context.aligned⟩ installed returned run
  refine ⟨result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=target.clock} at frame
  rw [CallNormal.continuationEntry,frame]

end InitECandidate.Solver.Input.ExcessBlobCurrent

#print axioms InitECandidate.Solver.Input.ExcessBlobCurrent.resume

namespace InitECandidate.Solver.Input.TaylorCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Reinsert the actual caller locals and returned binding around a real
child frame. Only the caller's own tick is added to its actual spent clock. -/
theorem WorkspaceResult.caller {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {price : Nat}
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) (returned : ValueHOL 64)
    (funded : 1≤source.clock) (result : WorkspaceResult (callEntryStateHOLFinite source callee) target base price) :
    WorkspaceResult source (CallNormal.continuationEntry source target name returned) base (price+1) := by
  let ready:=CallNormal.continuationEntry source target name returned
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
    locals:=ready.locals,memory:=ready.memory,clock:=ready.clock}) result.state
  change ready={source with locals:=ready.locals,memory:=ready.memory,clock:=ready.clock} at projected
  refine ⟨projected,?_,?_⟩
  · intro query outside
    exact result.away query outside
  · have cost:=result.cost
    change source.clock-1-target.clock≤price at cost
    change source.clock-target.clock≤price+1
    omega

end InitECandidate.Solver.Input.TaylorCurrent

#print axioms InitECandidate.Solver.Input.TaylorCurrent.WorkspaceResult.caller

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem zero_words : Single.remainderWords 0#64=GasBudget.U256Division.zeroWords := by
  funext index
  simp [Single.remainderWords,GasBudget.U256Division.zeroWords]

/-- The actual word-divisor wrapper covers zero as well as both positive
digit widths. Its real zero-divisor path returns zero without touching memory. -/
theorem divide_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (small : divisor.toNat≤2^63) :
    source.clock-(evaluateHOLFiniteState source GasBudget.U256Division.divBody).2.clock≤327 := by
  by_cases zero : divisor=0#64
  · subst divisor
    rw [zero_words] at bLocal
    have cost:=GasBudget.U256Division.div_zero_cost source a aLocal bLocal installed
    omega
  · have positive : 0<divisor.toNat:=by
      by_contra absent
      apply zero
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,Nat.zero_mod]
      omega
    by_cases one : divisor.toNat<4294967296
    · have cost:=U256.divide_cost source base divisor a context installed aLocal bLocal one positive
      omega
    · exact U256Double.divide_cost source base divisor a context installed aLocal bLocal (by omega) small

/-- A genuine return supplies the real quotient quad and the same physical
workspace frame for zero, one-digit and two-digit word divisors. -/
theorem divide_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (small : divisor.toNat≤2^63) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source GasBudget.U256Division.divBody=(some (.returned returned),post)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧ TaylorCurrent.WorkspaceResult source post base 327 := by
  have cost:=divide_cost source base divisor a context installed aLocal bLocal small
  rw [normal] at cost
  by_cases zero : divisor=0#64
  · subst divisor
    rw [zero_words] at bLocal
    have returnedEq:=GasBudget.U256Division.div_zero_normal source post a aLocal bLocal installed returned normal
    have frame:=GasBudget.U256Division.div_zero_frame source a aLocal bLocal installed
    rw [normal] at frame
    exact ⟨GasBudget.U256Division.zeroWords,returnedEq,TaylorCurrent.WorkspaceResult.of_erase frame cost⟩
  · have positive : 0<divisor.toNat:=by
      by_contra absent
      apply zero
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,Nat.zero_mod]
      omega
    by_cases one : divisor.toNat<4294967296
    · obtain ⟨quotient,funded,returnedEq,result⟩:=U256.divide_normal source post base divisor a context installed aLocal bLocal one positive returned normal
      have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
        locals:=post.locals,memory:=post.memory,clock:=post.clock}) result.state
      change post={source with locals:=post.locals,memory:=post.memory,clock:=post.clock} at frame
      refine ⟨quotient,returnedEq,⟨frame,?_,cost⟩⟩
      intro query outside
      exact result.away query (outside .quotient) (outside .remainder) (outside .divisor)
        (by intro index inside;exact outside .numerator index (by change index<16;omega))
    · obtain ⟨quotient,returnedEq,result⟩:=U256Double.divide_normal source post base divisor a context installed aLocal bLocal (by omega) small returned normal
      refine ⟨quotient,returnedEq,⟨result.state,?_,cost⟩⟩
      intro query outside
      exact result.away query (outside .normalizedNumerator) (outside .normalizedDivisor) (outside .quotient)
        (outside .remainder) (outside .divisor) (by intro index inside;exact outside .numerator index (by change index<16;omega))

/-- Real scoped calls reconstruct the current quotient caller at the
child's actual clock, with no assumed future success or worst-case funding. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64) (a : Quad)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code) (small : divisor.toNat≤2^63)
    (name : String) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "u256_div")
      [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ quotient,returned=RlpWrite.U256Value.tuple quotient ∧
      TaylorCurrent.WorkspaceResult (callEntryStateHOLFinite source callee) target base 327 ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple quotient) {source with memory:=target.memory,clock:=target.clock} := by
  obtain ⟨expected,lookup,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_div")
    GasBudget.U256Division.divBody RlpWrite.U256Value.tupleShape a (Single.remainderWords divisor) (GasBudget.U256Division.div_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=GasBudget.U256Division.divBody:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at aCell bCell
  rw [bodyEq] at run
  obtain ⟨quotient,returnedEq,result⟩:=divide_normal_frame (callEntryStateHOLFinite source callee) target base divisor a
    ⟨context.global,context.domain,context.arena,context.aligned⟩ installed aCell bCell small returned run
  refine ⟨quotient,returnedEq,result,?_⟩
  have frame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) result.state
  change {target with locals:=source.locals}={source with memory:=target.memory,clock:=target.clock} at frame
  rw [CallNormal.continuationEntry,returnedEq,frame]

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word.divide_cost
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word.divide_normal_frame
#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word.resume

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A checked readonly child changes only the caller's new local binding and
clock. Its genuine checked return supplies the current continuation entry. -/
theorem scoped_readonly_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (body continuation : ProgHOL 64) (returnShape : ShapeHOL) (price tailPrice : Nat)
    (code : source.code.lookup function=some (formals,body,returnShape))
    (priced : Bound source.code body price) (readonly : LocalEffects.Preserves source.code body)
    (tail : ∀ clock returned,shapeEqHOL (shapeOfHOLExact returned) shape=true →
      (setVarHOLFinite (ofString name) returned {source with clock:=clock}).clock-
        (evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock:=clock}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2.clock≤price+tailPrice+1 := by
  apply scoped_arguments_reached_current source name shape function arguments continuation price tailPrice
  · intro values actual callee actualShape args called
    have bodyEq:=LocalEffects.lookup_body source.code function formals body returnShape code values actual callee actualShape called
    rw [bodyEq]
    exact priced (callEntryStateHOLFinite source callee) rfl
  · intro values actual callee actualShape target returned args called run valid
    have bodyEq:=LocalEffects.lookup_body source.code function formals body returnShape code values actual callee actualShape called
    rw [bodyEq] at run
    have frame:=readonly (callEntryStateHOLFinite source callee) rfl
    rw [run] at frame
    change LocalEffects.erase target=LocalEffects.erase source at frame
    have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
      locals:=source.locals,clock:=target.clock}) frame
    have entryEq : CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) returned {source with clock:=target.clock}:=
      congrArg (setVarHOLFinite (ofString name) returned) callerFrame
    rw [entryEq]
    exact tail target.clock returned (Bool.and_eq_true_iff.mp valid).1

end InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current arithmetic scopes specialize the shared readonly-child rule. -/
theorem scoped_cost_current (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment source.code) (name : String) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (price tailPrice : Nat) (checked : kind.fixedPrice=some price)
    (tail : ∀ clock returned,shapeEqHOL (shapeOfHOLExact returned) shape=true →
      (setVarHOLFinite (ofString name) returned {source with clock:=clock}).clock-
        (evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock:=clock}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) shape kind.name arguments continuation)).2.clock≤price+tailPrice+1 :=
  Input.ClockCost.scoped_readonly_current source name shape kind.name arguments kind.signature.1 kind.body continuation kind.signature.2.2 price tailPrice
    (environment kind) (fixed_price kind price source.code environment checked) (original_preserves kind source.code environment) tail

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.Input.ClockCost.scoped_readonly_current
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.scoped_cost_current

namespace InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem argument_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (divisor : BitVec 64)
    (first second : ExpHOL 64) (installed : OriginalCode.Installed source.code)
    (den : eval source second=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second]=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "u256_div") values=some (actual,callee,shape)) :
    ∃ a : Quad,values=[RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple (Single.remainderWords divisor)] ∧
      actual=GasBudget.U256Division.divBody ∧
      callee.lookup (ofString "a")=some (RlpWrite.U256Value.tuple a) ∧
      callee.lookup (ofString "b")=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)) := by
  cases read : eval source first with
  | none=>
    simp only [eval] at read
    simp [evalListHOLFinite,evalListHOLExact,read] at args
  | some value=>
    have actualArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second]=
        some [value,RlpWrite.U256Value.tuple (Single.remainderWords divisor)]:=by
      simp only [eval] at read den
      simp [evalListHOLFinite,evalListHOLExact,read,den]
    have valuesEq:=Option.some.inj (args.symm.trans actualArgs)
    subst values
    obtain ⟨a,valueEq⟩:=TaylorCurrent.first_quad source.code.lookup (ofString "u256_div") GasBudget.U256Division.divBody value
      (Single.remainderWords divisor) actual callee shape (GasBudget.U256Division.div_code source.code installed) called
    subst value
    obtain ⟨expected,lookup,aCell,bCell⟩:=RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_div")
      GasBudget.U256Division.divBody RlpWrite.U256Value.tupleShape a (Single.remainderWords divisor) (GasBudget.U256Division.div_code source.code installed)
    have same:=Option.some.inj (called.symm.trans lookup)
    have bodyEq : actual=GasBudget.U256Division.divBody:=congrArg Prod.fst same
    have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    rw [←calleeEq] at aCell bCell
    exact ⟨a,rfl,bodyEq,aCell,bCell⟩

/-- A current scalar denominator prices the real two-quad scoped ABI.
Only a successful current lookup derives its numerator quad. The normal
continuation may depend on its actual quotient and restored caller locals. -/
theorem scoped_cost_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base divisor : BitVec 64)
    (context : Workspace.Context source base) (installed : OriginalCode.Installed source.code) (small : divisor.toNat≤2^63)
    (name : String) (first second : ExpHOL 64) (continuation : ProgHOL 64) (tailPrice : Nat)
    (den : eval source second=some (RlpWrite.U256Value.tuple (Single.remainderWords divisor)))
    (tail : ∀ memory clock quotient,
      (setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple quotient) {source with memory:=memory,clock:=clock}).clock-
        (evaluateHOLFiniteState (setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple quotient) {source with memory:=memory,clock:=clock}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape
      (ofString "u256_div") [first,second] continuation)).2.clock≤327+tailPrice+1 := by
  apply ClockCost.scoped_arguments_reached_current source name RlpWrite.U256Value.tupleShape (ofString "u256_div") [first,second] continuation 327 tailPrice
  · intro values actual callee shape args called
    obtain ⟨a,valuesEq,bodyEq,aCell,bCell⟩:=argument_entry source divisor first second installed den values actual callee shape args called
    rw [bodyEq]
    exact divide_cost (callEntryStateHOLFinite source callee) base divisor a
      ⟨context.global,context.domain,context.arena,context.aligned⟩ installed aCell bCell small
  · intro values actual callee shape target returned args called run valid
    obtain ⟨a,valuesEq,bodyEq,aCell,bCell⟩:=argument_entry source divisor first second installed den values actual callee shape args called
    rw [valuesEq] at called
    obtain ⟨quotient,returnedEq,result,entryEq⟩:=resume source target base divisor a context installed small name actual callee shape called returned run
    rw [entryEq]
    exact tail target.memory target.clock quotient

end InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word

#print axioms InitECandidate.Solver.Input.UDivMod.WideDigits.U256Word.scoped_cost_current

namespace InitECandidate.Solver.Input.BaseFeeCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_calculate_base_fee_per_gas with | .function fn=>progToHOL fn.body | _=>.skip
def targetExpression : ExpHOL 64:=.shift .lsr (localVar "parent_gas_limit") (.const 1#64)
def increaseSum : ProgHOL 64:=.decCall (ofString "r") RlpWrite.U256Value.tupleShape (ofString "u256_add")
  [localVar "parent_base_fee",localVar "bfd"] (.return (localVar "r"))
def increaseFinish : ProgHOL 64:=.seq
  (.ite (.cmp .notEqual (localVar "z") (.const 0#64))
    (.call (some (some (.local,ofString "bfd"),none)) (ofString "u256_from_word") [.const 1#64]) .skip) increaseSum
def increaseAfterSecond : ProgHOL 64:=.decCall (ofString "z") .one (ofString "u256_is_zero") [localVar "bfd"] increaseFinish
def increaseAfterFirst : ProgHOL 64:=.decCall (ofString "bfd") RlpWrite.U256Value.tupleShape (ofString "u256_div")
  [localVar "tfd",localVar "eight"] increaseAfterSecond
def increaseAfterProduct : ProgHOL 64:=.decCall (ofString "tfd") RlpWrite.U256Value.tupleShape (ofString "u256_div")
  [localVar "pfd",localVar "tgt"] increaseAfterFirst
def increaseAfterDelta : ProgHOL 64:=.decCall (ofString "pfd") RlpWrite.U256Value.tupleShape (ofString "u256_mul")
  [localVar "parent_base_fee",localVar "delta"] increaseAfterProduct
def increase : ProgHOL 64:=.decCall (ofString "delta") RlpWrite.U256Value.tupleShape (ofString "u256_from_word")
  [.op .sub [localVar "parent_gas_used",localVar "parent_gas_target"]] increaseAfterDelta
def decreaseSum : ProgHOL 64:=.decCall (ofString "r2") RlpWrite.U256Value.tupleShape (ofString "u256_sub")
  [localVar "parent_base_fee",localVar "bfd2"] (.return (localVar "r2"))
def decreaseAfterFirst : ProgHOL 64:=.decCall (ofString "bfd2") RlpWrite.U256Value.tupleShape (ofString "u256_div")
  [localVar "tfd2",localVar "eight"] decreaseSum
def decreaseAfterProduct : ProgHOL 64:=.decCall (ofString "tfd2") RlpWrite.U256Value.tupleShape (ofString "u256_div")
  [localVar "pfd2",localVar "tgt"] decreaseAfterFirst
def decreaseAfterDelta : ProgHOL 64:=.decCall (ofString "pfd2") RlpWrite.U256Value.tupleShape (ofString "u256_mul")
  [localVar "parent_base_fee",localVar "delta2"] decreaseAfterProduct
def decrease : ProgHOL 64:=.decCall (ofString "delta2") RlpWrite.U256Value.tupleShape (ofString "u256_from_word")
  [.op .sub [localVar "parent_gas_target",localVar "parent_gas_used"]] decreaseAfterDelta
def arithmetic : ProgHOL 64:=.seq
  (.ite (.cmp .lower (localVar "parent_gas_target") (localVar "parent_gas_used")) increase .skip) decrease
def afterTargetQuad : ProgHOL 64:=.decCall (ofString "eight") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [.const 8#64] arithmetic
def conversions : ProgHOL 64:=.decCall (ofString "tgt") RlpWrite.U256Value.tupleShape (ofString "u256_from_word") [localVar "parent_gas_target"] afterTargetQuad
def afterCheck : ProgHOL 64:=.seq
  (.ite (.cmp .equal (localVar "ok") (.const 0#64)) (.raise (ofString "BlockErr") (.const 10#64)) .skip)
  (.seq (.ite (.cmp .equal (localVar "parent_gas_used") (localVar "parent_gas_target")) (.return (localVar "parent_base_fee")) .skip) conversions)
def afterTarget : ProgHOL 64:=.decCall (ofString "ok") .one (ofString "check_gas_limit")
  [localVar "block_gas_limit",localVar "parent_gas_limit"] afterCheck

theorem body_shape : body=.dec (ofString "parent_gas_target") .one targetExpression afterTarget := by
  simp [body,Guest.Software.guestFn_calculate_base_fee_per_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    targetExpression,afterTarget,afterCheck,conversions,afterTargetQuad,arithmetic,increase,increaseAfterDelta,increaseAfterProduct,
    increaseAfterFirst,increaseAfterSecond,increaseFinish,increaseSum,decrease,decreaseAfterDelta,decreaseAfterProduct,
    decreaseAfterFirst,decreaseSum,localVar,RlpWrite.U256Value.tupleShape]

/-- Only the actual denominator tuples and their genuine workspace are
needed for arithmetic pricing. Other malformed values stop at their real ABI. -/
structure Model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) : Prop where
  context : UDivMod.WideDigits.Workspace.Context source base
  installed : OriginalCode.Installed source.code
  small : target.toNat≤2^63
  targetCell : source.locals.lookup (ofString "tgt")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad target))
  eightCell : source.locals.lookup (ofString "eight")=some (RlpWrite.U256Value.tuple (GasBudget.U256Multiply.wordQuad 8#64))

theorem Model.stage {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base target : BitVec 64} (model : Model source base target)
    (memory : BitVec 64→HolWordLab 64) (clock : Nat) (name : MlS) (value : ValueHOL 64)
    (notTarget : name≠ofString "tgt") (notEight : name≠ofString "eight") :
    Model (setVarHOLFinite name value {source with memory:=memory,clock:=clock}) base target := by
  refine ⟨⟨model.context.global,model.context.domain,model.context.arena,model.context.aligned⟩,model.installed,model.small,?_,?_⟩
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notTarget,Ne.symm notTarget] using model.targetCell
  · simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notEight,Ne.symm notEight] using model.eightCell

private theorem Model.target_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base target : BitVec 64} (model : Model source base target) :
    eval source (localVar "tgt")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords target)) := by
  have cell:=model.targetCell
  rw [GasBudget.U256Multiply.wordQuad_remainder] at cell
  simp [eval,localVar,evalHOLExact,toExact,cell]

private theorem Model.eight_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {base target : BitVec 64} (model : Model source base target) :
    eval source (localVar "eight")=some (RlpWrite.U256Value.tuple (UDivMod.WideDigits.Single.remainderWords 8#64)) := by
  have cell:=model.eightCell
  rw [GasBudget.U256Multiply.wordQuad_remainder] at cell
  simp [eval,localVar,evalHOLExact,toExact,cell]

/-- A selected increasing-fee branch always stops or returns. It cannot
fall through and execute the decreasing-fee branch in the same run. -/
theorem increase_stops : NoFallthrough increase := by
  unfold increase increaseAfterDelta increaseAfterProduct increaseAfterFirst increaseAfterSecond increaseFinish increaseSum
  repeat first | apply NoFallthrough.scoped | apply NoFallthrough.sequence | exact NoFallthrough.returned _

theorem increase_after_second_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code increaseAfterSecond 3 := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  have sum : ClockCost.Bound code increaseSum 1:=
    ClockCost.scoped_body code _ _ _ _ _ _ _ _ 0 0 (environment .u256_add)
      (GasBudget.ArithmeticEffects.price_u256_add code environment) (ClockCost.returned code _)
  have assigned : ClockCost.Bound code (.call (some (some (.local,ofString "bfd"),none)) (ofString "u256_from_word") [.const 1#64]) 1:=
    ClockCost.call_body code (some (some (ofString "bfd"))) _ _ _ _ _ 0 (environment .u256_from_word)
      (GasBudget.ArithmeticEffects.price_u256_from_word code environment)
  have finish : ClockCost.Bound code increaseFinish 2:=
    ClockCost.sequence code _ _ 1 1 (ClockCost.conditional code _ _ _ 1 0 assigned (ClockCost.skip code)) sum
  exact ClockCost.scoped_body code _ _ _ _ _ _ _ _ 0 2 (environment .u256_is_zero)
    (GasBudget.ArithmeticEffects.price_u256_is_zero code environment) finish

theorem increase_after_first_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source increaseAfterFirst).2.clock≤331 := by
  apply UDivMod.WideDigits.U256Word.scoped_cost_current source base 8#64 model.context model.installed (by decide)
    "bfd" (localVar "tfd") (localVar "eight") increaseAfterSecond 3 model.eight_read
  intro memory clock quotient
  exact increase_after_second_cost source.code model.installed _ rfl

theorem increase_after_product_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source increaseAfterProduct).2.clock≤659 := by
  apply UDivMod.WideDigits.U256Word.scoped_cost_current source base target model.context model.installed model.small
    "tfd" (localVar "pfd") (localVar "tgt") increaseAfterFirst 331 model.target_read
  intro memory clock quotient
  exact increase_after_first_cost _ base target (model.stage memory clock (ofString "tfd") _ (by decide) (by decide))

theorem increase_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source increase).2.clock≤668 := by
  apply GasBudget.ArithmeticEffects.scoped_cost_current .u256_from_word source
    (GasBudget.ArithmeticEffects.current_environment source.code model.installed) "delta" RlpWrite.U256Value.tupleShape _ increaseAfterDelta 0 667 rfl
  intro clock delta typed
  have next:=model.stage source.memory clock (ofString "delta") delta (by decide) (by decide)
  apply GasBudget.ArithmeticEffects.scoped_cost_current .u256_mul _
    (GasBudget.ArithmeticEffects.current_environment _ next.installed) "pfd" RlpWrite.U256Value.tupleShape _ increaseAfterProduct 7 659 rfl
  intro secondClock product productTyped
  exact increase_after_product_cost _ base target (next.stage _ secondClock (ofString "pfd") product (by decide) (by decide))

theorem decrease_sum_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code decreaseSum 1 := by
  have environment:=GasBudget.ArithmeticEffects.current_environment code installed
  exact ClockCost.scoped_body code _ _ _ _ _ _ _ _ 0 0 (environment .u256_sub)
    (GasBudget.ArithmeticEffects.price_u256_sub code environment) (ClockCost.returned code _)

theorem decrease_after_first_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source decreaseAfterFirst).2.clock≤329 := by
  apply UDivMod.WideDigits.U256Word.scoped_cost_current source base 8#64 model.context model.installed (by decide)
    "bfd2" (localVar "tfd2") (localVar "eight") decreaseSum 1 model.eight_read
  intro memory clock quotient
  exact decrease_sum_cost source.code model.installed _ rfl

theorem decrease_after_product_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source decreaseAfterProduct).2.clock≤657 := by
  apply UDivMod.WideDigits.U256Word.scoped_cost_current source base target model.context model.installed model.small
    "tfd2" (localVar "pfd2") (localVar "tgt") decreaseAfterFirst 329 model.target_read
  intro memory clock quotient
  exact decrease_after_first_cost _ base target (model.stage memory clock (ofString "tfd2") _ (by decide) (by decide))

theorem decrease_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source decrease).2.clock≤666 := by
  apply GasBudget.ArithmeticEffects.scoped_cost_current .u256_from_word source
    (GasBudget.ArithmeticEffects.current_environment source.code model.installed) "delta2" RlpWrite.U256Value.tupleShape _ decreaseAfterDelta 0 665 rfl
  intro clock delta typed
  have next:=model.stage source.memory clock (ofString "delta2") delta (by decide) (by decide)
  apply GasBudget.ArithmeticEffects.scoped_cost_current .u256_mul _
    (GasBudget.ArithmeticEffects.current_environment _ next.installed) "pfd2" RlpWrite.U256Value.tupleShape _ decreaseAfterProduct 7 657 rfl
  intro secondClock product productTyped
  exact decrease_after_product_cost _ base target (next.stage _ secondClock (ofString "pfd2") product (by decide) (by decide))

theorem arithmetic_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64) (model : Model source base target) :
    source.clock-(evaluateHOLFiniteState source arithmetic).2.clock≤668 :=
  ClockCost.stopping_guard_current source _ increase decrease 668 666 (increase_stops source)
    (increase_cost source base target model) (decrease_cost source base target model)

end InitECandidate.Solver.Input.BaseFeeCurrent

#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.body_shape
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.Model.stage
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.increase_stops
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.increase_after_second_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.increase_after_first_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.increase_after_product_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.increase_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.decrease_sum_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.decrease_after_first_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.decrease_after_product_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.decrease_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.arithmetic_cost

namespace InitECandidate.Solver.Input.BaseFeeCurrent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original shift produces a scalar strictly below 2^63 whenever
its actual read succeeds, independently of later gas-limit acceptance. -/
theorem target_read_small (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (read : eval source targetExpression=some value) :
    ∃ target : BitVec 64,value=.val (.word target) ∧ target.toNat≤2^63 := by
  cases cell : source.locals.lookup (ofString "parent_gas_limit") with
  | none=>simp [eval,targetExpression,evalHOLExact,toExact,localVar,cell] at read
  | some original=>
    cases original with
    | val payload=>
      cases payload with
      | word limit=>
        have expected : eval source targetExpression=some (.val (.word (limit>>>(1:Nat)))):=by
          simp [eval,targetExpression,evalHOLExact,toExact,localVar,cell,wordShiftHOL]
        refine ⟨limit>>>(1:Nat),Option.some.inj (read.symm.trans expected),?_⟩
        rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
        have bounded:=limit.isLt
        omega
    | rStruct fields | nStruct constructor fields=>simp [eval,targetExpression,evalHOLExact,toExact,localVar,cell] at read

/-- Both actual from-word declarations introduce the genuine denominator
tuples. No future successful arithmetic call or loop result is supplied. -/
theorem conversions_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (small : target.toNat≤2^63)
    (targetCell : source.locals.lookup (ofString "parent_gas_target")=some (.val (.word target))) :
    source.clock-(evaluateHOLFiniteState source conversions).2.clock≤670 := by
  let withTarget:=TaylorCurrent.tupleEntry source "tgt" target
  let withEight:=TaylorCurrent.tupleEntry withTarget "eight" 8#64
  have model : Model withEight base target:=by
    refine ⟨⟨context.global,context.domain,context.arena,context.aligned⟩,installed,small,?_,?_⟩
    · simp [withEight,withTarget,TaylorCurrent.tupleEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    · simp [withEight,TaylorCurrent.tupleEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have tail:=arithmetic_cost withEight base target model
  have eightCost:=TaylorCurrent.from_word_cost withTarget 8#64 installed "eight" [.const 8#64] arithmetic 668 rfl tail
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "parent_gas_target"]=some [.val (.word target)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,targetCell]
  exact TaylorCurrent.from_word_cost source target installed "tgt" [localVar "parent_gas_target"] afterTargetQuad 669 args eightCost

theorem after_check_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (small : target.toNat≤2^63)
    (targetCell : source.locals.lookup (ofString "parent_gas_target")=some (.val (.word target))) :
    source.clock-(evaluateHOLFiniteState source afterCheck).2.clock≤670 := by
  unfold afterCheck
  apply ClockCost.stopping_guard_current source _ (.raise (ofString "BlockErr") (.const 10#64)) _ 0 670
    (NoFallthrough.raised _ _ source) (ClockCost.raised _ _ _ source rfl)
  exact ClockCost.stopping_guard_current source _ (.return (localVar "parent_base_fee")) conversions 0 670
    (NoFallthrough.returned _ source) (ClockCost.returned _ _ source rfl)
    (conversions_cost source base target context installed small targetCell)

/-- The real gas-limit check is readonly and costs 66 body ticks. Its
actual checked scope preserves the already derived scalar target. -/
theorem after_target_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base target : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (small : target.toNat≤2^63)
    (targetCell : source.locals.lookup (ofString "parent_gas_target")=some (.val (.word target))) :
    source.clock-(evaluateHOLFiniteState source afterTarget).2.clock≤737 := by
  apply ClockCost.scoped_readonly_current source "ok" .one (ofString "check_gas_limit") _ CurrentVerify.GasLimit.formals
    CurrentVerify.GasLimit.body afterCheck .one 66 670 (CurrentVerify.GasLimit.original_code source.code installed)
    (CurrentVerify.GasLimit.body_cost source.code installed) (CurrentVerify.GasLimit.readonly source.code installed)
  intro clock returned typed
  apply after_check_cost (setVarHOLFinite (ofString "ok") returned {source with clock:=clock}) base target
    ⟨context.global,context.domain,context.arena,context.aligned⟩ installed small
  simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using targetCell

/-- Complete unchanged base-fee calculation at every incoming clock. Its
actual shift supplies the word-divisor range; zero returns zero, and either
real increasing/decreasing branch is bounded without future-success inputs. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤737 := by
  rw [body_shape]
  apply ClockCost.declared_reached_current
  intro value read typed
  obtain ⟨target,rfl,small⟩:=target_read_small source value read
  apply after_target_cost (setVarHOLFinite (ofString "parent_gas_target") (.val (.word target)) source) base target
    ⟨context.global,context.domain,context.arena,context.aligned⟩ installed small
  simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "calculate_base_fee_per_gas")=some
      ([(ofString "block_gas_limit",.one),(ofString "parent_gas_limit",.one),(ofString "parent_gas_used",.one),
        (ofString "parent_base_fee",RlpWrite.U256Value.tupleShape)],body,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 217
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_calculate_base_fee_per_gas) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_calculate_base_fee_per_gas,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Every ordinary caller form adds its own real call tick. Failed ABI
checks and malformed helper inputs stop within the same bound. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (context : UDivMod.WideDigits.Workspace.Context source base) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "calculate_base_fee_per_gas") arguments)).2.clock≤738 := by
  apply ClockCost.call_arguments_current source destination (ofString "calculate_base_fee_per_gas") arguments 737
  intro values actual callee shape args called
  have same:=LocalEffects.lookup_body source.code (ofString "calculate_base_fee_per_gas") _ body RlpWrite.U256Value.tupleShape
    (original_code source.code installed) values actual callee shape called
  rw [same]
  exact body_cost (callEntryStateHOLFinite source callee) base ⟨context.global,context.domain,context.arena,context.aligned⟩ installed

end InitECandidate.Solver.Input.BaseFeeCurrent

#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.target_read_small
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.conversions_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.after_check_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.after_target_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.body_cost
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.original_code
#print axioms InitECandidate.Solver.Input.BaseFeeCurrent.call_cost

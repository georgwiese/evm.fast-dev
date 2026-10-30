import InitECandidate.Solver.GasBudget.Mul64Value
import InitECandidate.Solver.Input.UDivMod.CurrentFrame
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostCurrentValue
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

import InitECandidate.Solver.GasBudget.ExponentPrice
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.Exponent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

/-- Invalid source argument values fail the real lookup before entering the
loop; valid shapes supply four actual words. Thus the price is uniform even
over malformed local environments. -/
theorem length_call_any_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : ArithmeticEffects.Environment source.code) :
    source.clock - (evaluateHOLFiniteState source
      (.decCall (ofString "len") .one (ofString "u256_bit_length") [localVar "b"] afterLength)).2.clock ≤ 4866 := by
  classical
  cases b : source.locals.lookup (ofString "b") with
  | none =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, b]
  | some value =>
    by_cases shape : shapeOfHOLExact value = U256Value.tupleShape
    · obtain ⟨words, valueEq⟩ := U256Value.of_shape value shape
      exact length_call_price source environment words (b.trans (congrArg some valueEq))
    · have code := environment .u256_bit_length
      rw [bits_signature] at code
      change source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one) at code
      have invalid : ¬shapeEqHOL U256Value.tupleShape (shapeOfHOLExact value) = true := by
        rw [shapeEqHOL_eq_true]
        exact Ne.symm shape
      have raw : lookupCodeHOLExact source.code.lookup (ofString "u256_bit_length") [value] = none := by
        simp [lookupCodeHOLExact, code, U256Bits.formals, invalid]
      have called : lookupCodeHOLFinite source.code.lookup (ofString "u256_bit_length") [value] = none :=
        (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr raw
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, b, called]

/-- Uniform all-outcome bound for the complete unchanged u256_exp body:
two length-call clocks plus at most256 iterations of19 source clocks.
This does not count straight-line target instructions. -/
theorem full_body_price (code) (environment : ArithmeticEffects.Environment code) :
    Input.ClockCost.Bound code ArithmeticEffects.Kind.u256_exp.body 4866 := by
  classical
  intro source installed
  have env : ArithmeticEffects.Environment source.code := by rw [installed]; exact environment
  rw [original_body, evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i result readResult
    split
    · rw [evaluateHOLFiniteState_dec_total]
      simp only
      split
      · change source.clock - source.clock ≤ 4866
        omega
      · rename_i base readBase
        split
        · exact length_call_any_price (setVarHOLFinite (ofString "base") base (setVarHOLFinite (ofString "result") result source)) env
        · change source.clock - source.clock ≤ 4866
          omega
    · simp

theorem call_price (code) (environment : ArithmeticEffects.Environment code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination)
      (ofString "u256_exp") arguments) 4867 :=
  Input.ClockCost.call_body code destination (ofString "u256_exp") arguments _ _ _ 4866
    (environment .u256_exp) (full_body_price code environment)

theorem scoped_price (code) (environment : ArithmeticEffects.Environment code)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (price : Nat)
    (priced : Input.ClockCost.Bound code continuation price) :
    Input.ClockCost.Bound code (.decCall name shape (ofString "u256_exp") arguments continuation) (4867 + price) := by
  have bound := Input.ClockCost.scoped_body code name shape (ofString "u256_exp") arguments continuation _ _ _
    4866 price (environment .u256_exp) (full_body_price code environment) priced
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

end InitECandidate.Solver.GasBudget.Exponent

#print axioms InitECandidate.Solver.GasBudget.Exponent.length_call_any_price
#print axioms InitECandidate.Solver.GasBudget.Exponent.full_body_price
#print axioms InitECandidate.Solver.GasBudget.Exponent.call_price
#print axioms InitECandidate.Solver.GasBudget.Exponent.scoped_price

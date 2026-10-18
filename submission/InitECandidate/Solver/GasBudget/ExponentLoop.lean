import InitECandidate.Solver.GasBudget.ArithmeticClockPrice
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.GasBudget.Exponent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def quad : ShapeHOL := .comb [.one, .one, .one, .one]
def test : ExpHOL 64 := .cmp .lower (localVar "t") (localVar "len")
def multiply (destination left right : String) : ProgHOL 64 :=
  .call (some (some (.local, ofString destination), none)) (ofString "u256_mul") [localVar left, localVar right]
def bitProduct : ProgHOL 64 := .ite (.cmp .equal (localVar "bit") (.const 1#64)) (multiply "result" "result" "base") .skip
def square : ProgHOL 64 := .ite test (multiply "base" "base" "base") .skip
def increment : ProgHOL 64 := .assign .local (ofString "t") (.op .add [localVar "t", .const 1#64])
def tail : ProgHOL 64 := .seq bitProduct (.seq increment square)
def loopBody : ProgHOL 64 := .decCall (ofString "bit") .one (ofString "u256_bit") [localVar "b", localVar "t"] tail
def loop : ProgHOL 64 := .while test loopBody
def afterLength : ProgHOL 64 := .dec (ofString "t") .one (.const 0#64) (.seq loop (.return (localVar "result")))

/-- Reification of the complete unchanged exponentiation body. -/
theorem original_body : ArithmeticEffects.Kind.u256_exp.body =
    .dec (ofString "result") quad (.rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64])
      (.dec (ofString "base") quad (localVar "a")
        (.decCall (ofString "len") .one (ofString "u256_bit_length") [localVar "b"] afterLength)) := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_exp, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    quad, afterLength, loop, test, loopBody, tail, bitProduct, square, multiply, increment, localVar]
  rfl

theorem multiply_safe (key : MlS) (destination left right : String) (other : key ≠ ofString destination) :
    Input.LocalPrefix key (multiply destination left right) := by
  apply Input.LocalPrefix.call (some (ofString destination))
  intro name equality
  cases equality
  exact other

theorem body_safe (key : MlS) (notBit : key ≠ ofString "bit") (notResult : key ≠ ofString "result")
    (notBase : key ≠ ofString "base") (notT : key ≠ ofString "t") : Input.LocalPrefix key loopBody :=
  .decCall _ _ _ _ notBit (.seq (.ite _ (multiply_safe key _ _ _ notResult) .skip)
    (.seq (.assign _ _ notT) (.ite _ (multiply_safe key _ _ _ notBase) .skip)))

theorem body_advances : Input.CounterFlow.Advances (ofString "t") 1 loopBody := by
  apply Input.CounterFlow.scoped_call _ "bit" _ _ _ _ _ (by decide)
  apply Input.CounterFlow.sequence _ _ _ 0 1
  · exact Input.CounterFlow.preserved _ _ (.ite _ (multiply_safe _ _ _ _ (by decide)) .skip)
  · apply Input.CounterFlow.sequence _ _ _ 1 0
    · exact Input.CounterFlow.increment _
    · exact Input.CounterFlow.preserved _ _ (.ite _ (multiply_safe _ _ _ _ (by decide)) .skip)

theorem multiply_price (code) (environment : ArithmeticEffects.Environment code) (destination left right : String) :
    Input.ClockCost.Bound code (multiply destination left right) 8 :=
  Input.ClockCost.call_body code (some (some (ofString destination))) (ofString "u256_mul") _ _ _ _ 7
    (environment .u256_mul) (ArithmeticEffects.price_u256_mul code environment)

theorem body_price (code) (environment : ArithmeticEffects.Environment code) : Input.ClockCost.Bound code loopBody 18 := by
  apply Input.ClockCost.scoped_body code _ _ (ofString "u256_bit") _ _ _ _ _ 1 16
    (environment .u256_bit) (ArithmeticEffects.price_u256_bit code environment)
  apply Input.ClockCost.sequence code _ _ 8 8
  · exact Input.ClockCost.conditional code _ _ _ 8 0 (multiply_price code environment _ _ _) (Input.ClockCost.skip code)
  · apply Input.ClockCost.sequence code _ _ 0 8
    · exact Input.ClockCost.assign code _ _
    · exact Input.ClockCost.conditional code _ _ _ 8 0 (multiply_price code environment _ _ _) (Input.ClockCost.skip code)

/-- Every actual exponentiation loop outcome spends at most19 source clocks
per remaining exponent bit. The real bit counter/limit are current-state
facts; no iteration trace, body success, or future clock is assumed. -/
theorem loop_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : ArithmeticEffects.Environment source.code)
    (counter : BitVec 64) (length : Nat) (small : length ≤ 256)
    (t : source.locals.lookup (ofString "t") = some (.val (.word counter)))
    (len : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : counter.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 19 * (length - counter.toNat) :=
  Input.CounterFlow.loop_cost source.code (ofString "t") (ofString "len") loopBody 18 length (by omega)
    (body_price source.code environment) body_advances (body_safe _ (by decide) (by decide) (by decide) (by decide))
    source counter rfl t len initial

end InitECandidate.Solver.GasBudget.Exponent

#print axioms InitECandidate.Solver.GasBudget.Exponent.original_body
#print axioms InitECandidate.Solver.GasBudget.Exponent.body_advances
#print axioms InitECandidate.Solver.GasBudget.Exponent.body_price
#print axioms InitECandidate.Solver.GasBudget.Exponent.loop_price

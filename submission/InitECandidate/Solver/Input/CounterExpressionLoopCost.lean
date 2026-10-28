import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

/-- Actual unsigned counter loops with a limit expression read from one
preserved local snapshot, such as a tuple field. All outcomes are bounded;
the read obligation concerns current locals only, with no future loop model. -/
theorem loop_expression_flow_cost (code) (counter captured : MlS) (snapshot : ValueHOL 64) (lengthExpression : ExpHOL 64)
    (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^64)
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalFlow captured body)
    (lengthRead : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.locals.lookup captured=some snapshot →
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) lengthExpression=some (.val (.word (BitVec.ofNat 64 length))))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup captured = some snapshot)
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while (.cmp .lower (.var .local counter) lengthExpression) body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  apply loop_snapshot_cost code counter captured (some snapshot) _ body price length lengthBound
  · intro current word currentCell capturedCell bounded
    have lengthMod : length % 18446744073709551616 = length := Nat.mod_eq_of_lt lengthBound
    have expressionRead := lengthRead current capturedCell
    change @evalHOLExact 64 Guest.HostMemory _ current.toExact
      (fun address => Classical.propDecidable (current.memaddrs address)) lengthExpression = _ at expressionRead
    simp [evalHOLFinite, evalHOLExact, currentCell, expressionRead, wordCmpHOL, BitVec.lt_def,
      BitVec.toNat_ofNat, lengthMod]
  · exact priced
  · exact advance
  · exact safe
  · exact installed
  · exact counterCell
  · exact limitCell
  · exact initial

theorem loop_expression_cost (code) (counter captured : MlS) (snapshot : ValueHOL 64) (lengthExpression : ExpHOL 64)
    (body : ProgHOL 64) (price length : Nat)
    (lengthBound : length < 2^64)
    (priced : ClockCost.Bound code body price)
    (advance : Advances counter 1 body) (safe : LocalPrefix captured body)
    (lengthRead : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.locals.lookup captured=some snapshot →
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) lengthExpression=some (.val (.word (BitVec.ofNat 64 length))))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : source.code = code)
    (counterCell : source.locals.lookup counter = some (.val (.word word)))
    (limitCell : source.locals.lookup captured = some snapshot)
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source (.while (.cmp .lower (.var .local counter) lengthExpression) body)).2.clock ≤
      (price + 1) * (length - word.toNat) := by
  exact loop_expression_flow_cost code counter captured snapshot lengthExpression body price length
    lengthBound priced advance (.base safe) lengthRead source word installed counterCell limitCell initial

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.loop_expression_cost

#print axioms InitECandidate.Solver.Input.CounterFlow.loop_expression_flow_cost

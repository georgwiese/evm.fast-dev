import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem sequence_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (front : source.clock - (evaluateHOLFiniteState source first).2.clock ≤ firstPrice)
    (back : Bound source.code second secondPrice) :
    source.clock - (evaluateHOLFiniteState source (.seq first second)).2.clock ≤ firstPrice + secondPrice := by
  have firstClock := evaluateHOLFiniteState_clock_le source first
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at front firstClock ⊢
  obtain ⟨result, middle⟩ := output
  change source.clock - middle.clock ≤ firstPrice at front
  change middle.clock ≤ source.clock at firstClock
  cases result with
  | none =>
    have codeEq := (Input.evaluation_fields source middle first none computed).2.2.2
    have secondCost := back middle codeEq
    have secondClock := evaluateHOLFiniteState_clock_le middle second
    change source.clock - (evaluateHOLFiniteState middle second).2.clock ≤ _
    omega
  | some result =>
    change source.clock - middle.clock ≤ _
    omega

theorem declared_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (price : Nat)
    (read : eval source expression = some (.val (.word word)))
    (priced : (bind source name word).clock - (evaluateHOLFiniteState (bind source name word) body).2.clock ≤ price) :
    source.clock - (evaluateHOLFiniteState source (.dec (ofString name) .one expression body)).2.clock ≤ price := by
  let output := evaluateHOLFiniteState (bind source name word) body
  have actual := ScalarScope.declare_execute source output.2 name expression word body output.1 read rfl
  rw [actual]
  exact priced

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.sequence_current
#print axioms InitECandidate.Solver.Input.ClockCost.declared_current

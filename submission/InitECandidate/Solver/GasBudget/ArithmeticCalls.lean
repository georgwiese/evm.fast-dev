import InitECandidate.Solver.GasBudget.ArithmeticPricedPrefix

namespace InitECandidate.Solver.GasBudget.ArithmeticCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Call where
  name : String
  shape : ShapeHOL
  helper : ArithmeticEffects.Kind
  arguments : List (ExpHOL 64)
  price : Nat
  checked : helper.fixedPrice = some price

def program : List Call → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | call :: calls, continuation => .decCall (ofString call.name) call.shape call.helper.name call.arguments (program calls continuation)

def budget : List Call → Nat
  | [] => 0
  | call :: calls => call.price + 1 + budget calls

/-- A literal chain of original priced arithmetic calls reaches its real
continuation with only locals/clock changed. Every callee return, shape check,
funding and total spent clock comes from actual execution. -/
theorem normal (calls : List Call) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : ArithmeticEffects.Environment source.code) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (program calls continuation) = (some (.returned value), post)) :
    ∃ paid ready inner, paid ≤ budget calls ∧ paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with clock := source.clock - paid} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  induction calls generalizing source post with
  | nil => exact ⟨0, source, post, by simp [budget], by omega, by simp, by simp, run, rfl⟩
  | cons call calls ih =>
    obtain ⟨positive, clock, returned, firstPost, earlier, cost, typed, restRun, postEq⟩ :=
      ArithmeticEffects.priced_scoped_prefix call.helper call.price call.checked source post environment call.name call.shape call.arguments (program calls continuation) value run
    let first := setVarHOLFinite (ofString call.name) returned {source with clock := clock}
    obtain ⟨paid, ready, inner, bounded, fits, readyClock, frameEq, continuationRun, innerEq⟩ :=
      ih first firstPost environment restRun
    have firstClock : first.clock = clock := rfl
    have sub : clock - paid = source.clock - ((source.clock - clock) + paid) := by omega
    have readyFrame : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with clock := source.clock - ((source.clock - clock) + paid)} := by
      change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with clock := clock - paid} at frameEq
      simpa only [sub] using frameEq
    refine ⟨(source.clock - clock) + paid, ready, inner, ?_, ?_, ?_, readyFrame, continuationRun, ?_⟩
    · change (source.clock - clock) + paid ≤ call.price + 1 + budget calls
      omega
    · rw [firstClock] at fits
      omega
    · rw [readyClock, firstClock, sub]
    · rw [postEq]
      exact innerEq

end InitECandidate.Solver.GasBudget.ArithmeticCalls

#print axioms InitECandidate.Solver.GasBudget.ArithmeticCalls.normal

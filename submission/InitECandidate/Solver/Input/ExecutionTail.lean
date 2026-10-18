import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual suffix executions connected through local restorations, ignored
returns and real continuations/handlers. Parent contracts derive these
steps from their original evaluator runs. This records the remaining
execution; it does not price it or assume physical-model preservation. -/
inductive ExecutionTail (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (suffix : ProgHOL 64) :
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 Guest.HostMemory → Prop where
  | run (result) (post) (actual : evaluateHOLFiniteState entry suffix = (result, post)) : ExecutionTail entry suffix result post
  | locals {result source target} (prior : ExecutionTail entry suffix result source)
      (same : emptyLocalsHOLFinite target = emptyLocalsHOLFinite source) : ExecutionTail entry suffix result target
  | ignored_return {returned target} (prior : ExecutionTail entry suffix (some (.returned returned)) target)
      (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (shape : ShapeHOL)
      (checked : shapeEqHOL (shapeOfHOLExact returned) shape = true) :
      ExecutionTail entry suffix none {target with locals := saved.locals}
  | ignored_exception {identifier payload target} (prior : ExecutionTail entry suffix (some (.exception identifier payload)) target) :
      ExecutionTail entry suffix (some (.exception identifier payload)) (emptyLocalsHOLFinite target)
  | next {middle result target} (prior : ExecutionTail entry suffix none middle) (continuation : ProgHOL 64)
      (actual : evaluateHOLFiniteState middle continuation = (result, target)) : ExecutionTail entry suffix result target
  | handler {identifier payload middle result target} (prior : ExecutionTail entry suffix (some (.exception identifier payload)) middle)
      (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (parameter : MlS) (handler : ProgHOL 64)
      (actual : evaluateHOLFiniteState (setVarHOLFinite parameter payload {middle with locals := saved.locals}) handler = (result, target)) :
      ExecutionTail entry suffix result target

private theorem actual_clock {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {program : ProgHOL 64}
    {result : Option (PanSemResultExact 64)} (actual : evaluateHOLFiniteState source program = (result, target)) :
    target.clock ≤ source.clock := by
  have clock := evaluateHOLFiniteState_clock_le source program
  rw [actual] at clock
  exact clock

/-- Recorded continuations only spend source clocks; lexical/call return
steps preserve the exact remaining clock. No suffix cost bound is claimed. -/
theorem ExecutionTail.clock_le {entry target : PanSemStateFiniteExact 64 Guest.HostMemory} {suffix : ProgHOL 64}
    {result : Option (PanSemResultExact 64)} (tail : ExecutionTail entry suffix result target) :
    target.clock ≤ (evaluateHOLFiniteState entry suffix).2.clock := by
  induction tail with
  | run result post actual => rw [actual]
  | locals prior same ih =>
    have clock := congrArg PanSemStateFiniteExact.clock same
    change _ = _ at clock
    exact clock.le.trans ih
  | ignored_return prior saved shape checked ih => exact ih
  | ignored_exception prior ih => exact ih
  | next prior continuation actual ih =>
    exact (actual_clock actual).trans ih
  | handler prior saved parameter handler actual ih =>
    exact (actual_clock actual).trans ih

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ExecutionTail.clock_le

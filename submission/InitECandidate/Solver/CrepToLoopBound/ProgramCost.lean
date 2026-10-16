import InitECandidate.Solver.CrepToLoopBound.ExpressionCost
import Flapjack.Pancake.Semantics.CrepProps

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack

/-- Local administrative overhead. A source call or loop decrement pays for
recursive bodies; the ceiling separately covers every nested continuation. -/
def cost {width : Nat} [NeZero width] : CrepProgHOL width → Nat
  | .dec _ value body => expCost value + cost body
  | .assign _ value | .storeGlob _ value | .shMem _ _ value => expCost value
  | .store address value | .store32 address value | .storeByte address value =>
      expCost address + expCost value
  | .seq first second => cost first + cost second
  | .ite condition first second => expCost condition + max (cost first) (cost second) + 1
  | .while condition _ => expCost condition + 2
  | .call _ _ arguments | .return arguments => expsCost arguments
  | _ => 0

def ceiling {width : Nat} [NeZero width] (program : CrepProgHOL width) : Nat :=
  max (cost program) (match program with
    | .dec _ _ body | .while _ body => ceiling body
    | .seq first second | .ite _ first second => max (ceiling first) (ceiling second)
    | .call ret _ _ => match ret with
        | some (_, some (_, handler)) => ceiling handler
        | _ => 0
    | _ => 0)

def CodeSafe {width : Nat} [NeZero width] (limit : Nat)
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) : Prop :=
  ∀ name parameters program, code.lookup name = some (parameters, program) → ceiling program ≤ limit

theorem cost_le_ceiling {width : Nat} [NeZero width] (program : CrepProgHOL width) :
    cost program ≤ ceiling program := by
  cases program <;> try exact Nat.le_max_left _ _
  rename_i ret name args
  cases ret with
  | none => exact Nat.le_max_left _ _
  | some descriptor =>
    rcases descriptor with ⟨names, handler⟩
    cases handler with
    | none => exact Nat.le_max_left _ _
    | some descriptor =>
      rcases descriptor with ⟨exception, body⟩
      exact Nat.le_max_left _ _

theorem codeSafe_evaluate {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {source post : CrepSemHOLState width F} {program : CrepProgHOL width}
    {result : Option (CrepResultHOLExact width)}
    (safe : CodeSafe limit source.code)
    (run : evalCrepSemHOLProgExact source program = (result, post)) : CodeSafe limit post.code := by
  rw [evaluateCodeInvariantHOL program source result post run]
  exact safe

theorem clockDecrease {width : Nat} [NeZero width] {F : Type}
    {source post : CrepSemHOLState width F} {program : CrepProgHOL width}
    {result : Option (CrepResultHOLExact width)}
    (run : evalCrepSemHOLProgExact source program = (result, post)) : post.clock ≤ source.clock := by
  classical
  have bound : (evalCrepSemHOLProgExact source program).2.clock ≤ source.clock := by
    rw [evalCrepSemHOLProgExact_eq_core source program
      (fun a => Classical.propDecidable (source.memaddrs a))
      (fun a => Classical.propDecidable (source.shMemaddrs a))]
    exact evalCrepSemHOLProg_clock_le source _ _ program
  simpa only [run] using bound

theorem seqCeiling {width : Nat} [NeZero width] (first second : CrepProgHOL width) (limit : Nat)
    (bound : ceiling (.seq first second) ≤ limit) : ceiling first ≤ limit ∧ ceiling second ≤ limit := by
  rw [ceiling] at bound
  omega

theorem decCeiling {width : Nat} [NeZero width] (name : Nat) (value : CrepExpHOL width)
    (body : CrepProgHOL width) (limit : Nat) (bound : ceiling (.dec name value body) ≤ limit) :
    ceiling body ≤ limit := by
  rw [ceiling] at bound
  omega

theorem ifCeiling {width : Nat} [NeZero width] (condition : CrepExpHOL width)
    (first second : CrepProgHOL width) (limit : Nat) (bound : ceiling (.ite condition first second) ≤ limit) :
    ceiling first ≤ limit ∧ ceiling second ≤ limit := by
  rw [ceiling] at bound
  omega

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.cost_le_ceiling
#print axioms InitECandidate.Solver.CrepToLoopBound.codeSafe_evaluate
#print axioms InitECandidate.Solver.CrepToLoopBound.clockDecrease
#print axioms InitECandidate.Solver.CrepToLoopBound.seqCeiling
#print axioms InitECandidate.Solver.CrepToLoopBound.decCeiling
#print axioms InitECandidate.Solver.CrepToLoopBound.ifCeiling

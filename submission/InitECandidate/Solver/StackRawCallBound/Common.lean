import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Optimized

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

/-- A positive-clock call reserves its own source-clock decrement. An enclosing
optimized tail sequence may spend this credit on its extra frame-growth tick. -/
def callCredit {width : Nat} [NeZero width] (program : HolProg width) (clock : Nat) : Nat :=
  match program with
  | .call .. | .rawCall .. => if clock = 0 then 0 else 1
  | _ => 0

/-- The original simulation, with a bound on the same existential extra clock.
The full state relation, evaluator equation and stack-space exceptions remain. -/
abbrev BoundedSimulation {width : Nat} [NeZero width] {C F : Type}
    (credit allowance : Nat) (compiled : HolProg width) (info : Spt Nat)
    (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) : Prop :=
  ∃ extra targetPost stackSpace,
    extra + credit ≤ allowance ∧
    stateRel info post targetPost ∧
    StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
      (result, {targetPost with stackSpace := stackSpace}) ∧
    (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
      stackSpace = targetPost.stackSpace)

abbrev BoundedProgramIH {width : Nat} [NeZero width] (C F : Type)
    (program : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    BoundedSimulation (callCredit program source.clock) (source.clock - post.clock)
      (comp info program) info target post result

abbrev BoundedSeqSecondIH {width : Nat} [NeZero width] (C F : Type)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ middle : StackSemStateFiniteExact width C F,
    StackSemEvaluate.evaluate (first, source) = (none, middle) →
    BoundedProgramIH C F second middle

theorem forgetBound {width : Nat} [NeZero width] {C F : Type}
    {credit allowance : Nat} {compiled : HolProg width} {info : Spt Nat}
    {target post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)}
    (bounded : BoundedSimulation credit allowance compiled info target post result) :
    IfCase.SimulationResult compiled info target post result := by
  obtain ⟨extra, targetPost, space, _, relation, execution, guard⟩ := bounded
  exact ⟨extra, targetPost, space, relation, execution, guard⟩

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.forgetBound

import InitECandidate.Solver.CrepToLoopBound.StraightClock
import Flapjack.Pancake.CrepToLoop.ContextExact

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack

mutual
  /-- Only comparisons introduce clocked cuts during expression compilation. -/
  def expCost {width : Nat} [NeZero width] : CrepExpHOL width → Nat
    | .load e | .load32 e | .loadByte e => expCost e
    | .op _ es | .crepOp _ es => expsCost es
    | .cmp _ first second => expCost first + expCost second + 1
    | .shift _ first second => expCost first + expCost second
    | _ => 0
  termination_by structural e => e

  def expsCost {width : Nat} [NeZero width] : List (CrepExpHOL width) → Nat
    | [] => 0
    | e :: es => expCost e + expsCost es
  termination_by structural es => es
end

def CodeCost {width : Nat} [NeZero width] (code : List (HolLoopProg width)) (budget : Nat) : Prop :=
  code.all straight = true ∧ (code.map charge).sum = budget

private theorem assignmentCost {width : Nat} [NeZero width]
    (names : List Nat) (values : List (HolLoopExp width)) (offset : Nat) :
    CodeCost (names.zipWith (fun name value => .assign (offset + name) value) values) 0 := by
  induction names generalizing values with
  | nil => simp [CodeCost]
  | cons name names ih =>
    cases values with
    | nil => simp [CodeCost]
    | cons value values => simpa [CodeCost, straight, charge] using ih values

private theorem crepopCost {width : Nat} [NeZero width]
    (operator : CrepOp) (target : Compiler.Encoders.Asm.AsmArchitecture) (left right tmp : Nat) (live : NumSet) :
    CodeCost (compileCrepopHOLExact (width := width) operator target left right tmp live).1 0 := by
  cases operator
  simp only [compileCrepopHOLExact]
  split <;> simp [CodeCost, straight, charge]

mutual
  theorem expressionCost {width : Nat} [NeZero width]
      (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (expression : CrepExpHOL width) :
      CodeCost (compileExpHOLExact context tmp live expression).1 (expCost expression) := by
    cases expression with
    | load body =>
      simpa only [compileExpHOLExact, expCost] using expressionCost context tmp live body
    | load32 body =>
      have ih := expressionCost context tmp live body
      rcases run : compileExpHOLExact context tmp live body with ⟨code, value, next, outLive⟩
      simp_all [compileExpHOLExact, expCost, CodeCost, straight, charge, List.all_append, List.sum_append]
    | loadByte body =>
      have ih := expressionCost context tmp live body
      rcases run : compileExpHOLExact context tmp live body with ⟨code, value, next, outLive⟩
      simp_all [compileExpHOLExact, expCost, CodeCost, straight, charge, List.all_append, List.sum_append]
    | op operator expressions =>
      simpa only [compileExpHOLExact, expCost] using expressionsCost context tmp live expressions
    | crepOp operator expressions =>
      have ih := expressionsCost context tmp live expressions
      rcases run : compileExpsHOLExact context tmp live expressions with ⟨code, values, next, outLive⟩
      have assigns := assignmentCost (List.range values.length) values next
      have opCost := crepopCost (width := width) operator context.target next (next + 1)
        (next + values.length) (sptListInsert ((List.range values.length).map (fun n => next + n)) outLive)
      simp_all [compileExpHOLExact, expCost, CodeCost, straight, charge, List.all_append, List.sum_append]
    | cmp operator first second =>
      have ih1 := expressionCost context tmp live first
      rcases run1 : compileExpHOLExact context tmp live first with ⟨code1, value1, next1, live1⟩
      have ih2 := expressionCost context next1 live1 second
      rcases run2 : compileExpHOLExact context next1 live1 second with ⟨code2, value2, next2, live2⟩
      simp_all [compileExpHOLExact, expCost, CodeCost, progIfHOLExact, straight, charge, List.all_append, List.sum_append, Nat.add_assoc]
    | shift operator first second =>
      have ih1 := expressionCost context tmp live first
      rcases run1 : compileExpHOLExact context tmp live first with ⟨code1, value1, next1, live1⟩
      have ih2 := expressionCost context next1 live1 second
      rcases run2 : compileExpHOLExact context next1 live1 second with ⟨code2, value2, next2, live2⟩
      simp_all [compileExpHOLExact, expCost, CodeCost, straight, charge, List.all_append, List.sum_append]
    | _ => simp [compileExpHOLExact, expCost, CodeCost]
  termination_by sizeOf expression

  theorem expressionsCost {width : Nat} [NeZero width]
      (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (expressions : List (CrepExpHOL width)) :
      CodeCost (compileExpsHOLExact context tmp live expressions).1 (expsCost expressions) := by
    cases expressions with
    | nil => simp [compileExpsHOLExact, expsCost, CodeCost]
    | cons expression expressions =>
      have ih1 := expressionCost context tmp live expression
      rcases run1 : compileExpHOLExact context tmp live expression with ⟨code1, value1, next1, live1⟩
      have ih2 := expressionsCost context next1 live1 expressions
      rcases run2 : compileExpsHOLExact context next1 live1 expressions with ⟨code2, value2, next2, live2⟩
      simp_all [compileExpsHOLExact, expsCost, CodeCost, List.all_append, List.sum_append]
  termination_by sizeOf expressions
end

theorem nestedSeqCost {width : Nat} [NeZero width] (code : List (HolLoopProg width)) (budget : Nat)
    (checked : CodeCost code budget) :
    straight (loopNestedSeqHOL code) = true ∧ charge (loopNestedSeqHOL code) = budget := by
  induction code generalizing budget with
  | nil => simpa [CodeCost, loopNestedSeqHOL, straight, charge] using checked
  | cons head tail ih =>
    have tailChecked : CodeCost tail (tail.map charge).sum :=
      ⟨(List.all_eq_true.mp checked.1 |> fun h => List.all_eq_true.mpr (fun x hx => h x (by simp [hx]))), rfl⟩
    have tailShape := ih _ tailChecked
    simp_all [CodeCost, loopNestedSeqHOL, straight, charge]

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.expressionCost
#print axioms InitECandidate.Solver.CrepToLoopBound.expressionsCost
#print axioms InitECandidate.Solver.CrepToLoopBound.nestedSeqCost

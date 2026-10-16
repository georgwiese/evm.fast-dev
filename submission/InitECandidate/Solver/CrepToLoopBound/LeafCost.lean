import InitECandidate.Solver.CrepToLoopBound.ProgramCost

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack

def Leaf {width : Nat} [NeZero width] : CrepProgHOL width → Bool
  | .dec .. | .seq .. | .ite .. | .while .. | .call .. | .tick => false
  | _ => true

private theorem assignsCost {width : Nat} [NeZero width]
    (names : List Nat) (values : List (HolLoopExp width)) :
    CodeCost (names.zipWith HolLoopProg.assign values) 0 := by
  induction names generalizing values with
  | nil => simp [CodeCost]
  | cons name names ih =>
    cases values with
    | nil => simp [CodeCost]
    | cons value values => simpa [CodeCost, straight, charge] using ih values

private theorem appendCost {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width)) (a b : Nat)
    (hfirst : CodeCost first a) (hsecond : CodeCost second b) :
    CodeCost (first ++ second) (a + b) := by
  simp_all [CodeCost, List.all_append, List.sum_append]

theorem leafCost {width : Nat} [NeZero width] (context : CrepToLoopContextExact)
    (live : NumSet) (program : CrepProgHOL width) (leaf : Leaf program = true) :
    straight (compileHOLExact context live program) = true ∧
      charge (compileHOLExact context live program) ≤ cost program := by
  cases program with
  | skip | «break» _ | «continue» _ | «raise» _ =>
    simp [compileHOLExact, straight, charge, cost]
  | dec _ _ _ | seq _ _ | ite _ _ _ | «while» _ _ | call _ _ _ | tick => simp [Leaf] at leaf
  | «return» expressions =>
    have expr := expressionsCost context (context.vmax + 1) live expressions
    rcases run : compileExpsHOLExact context (context.vmax + 1) live expressions with
      ⟨code, values, tmp, outLive⟩
    have assigns := assignsCost (genTemps tmp values.length) values
    have checked : CodeCost (code ++ (genTemps tmp values.length).zipWith HolLoopProg.assign values ++
        [.return (genTemps tmp values.length)]) (expsCost expressions) := by
      simp_all [CodeCost, straight, charge, List.all_append, List.sum_append]
    have shape := nestedSeqCost _ _ checked
    simpa [compileHOLExact, run, cost] using And.intro shape.1 (Nat.le_of_eq shape.2)
  | store address value =>
    have first := expressionCost context (context.vmax + 1) live address
    rcases run1 : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨code1, value1, tmp1, live1⟩
    have second := expressionCost context tmp1 live1 value
    rcases run2 : compileExpHOLExact context tmp1 live1 value with
      ⟨code2, value2, tmp2, live2⟩
    simp only [compileHOLExact, run1, run2]
    have shape := nestedSeqCost (width := width) (code1 ++ code2 ++ [.assign tmp2 value2, .store value1 tmp2])
      (expCost address + expCost value) (by
        simp_all [CodeCost, straight, charge, List.all_append, List.sum_append])
    exact ⟨shape.1, Nat.le_of_eq shape.2⟩
  | store32 address value =>
    have first := expressionCost context (context.vmax + 1) live address
    rcases run1 : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨code1, value1, tmp1, live1⟩
    have second := expressionCost context tmp1 live1 value
    rcases run2 : compileExpHOLExact context tmp1 live1 value with
      ⟨code2, value2, tmp2, live2⟩
    simp only [compileHOLExact, run1, run2]
    have shape := nestedSeqCost (width := width) (code1 ++ code2 ++ [.assign tmp2 value1, .assign (tmp2 + 1) value2, .store32 tmp2 (tmp2 + 1)])
      (expCost address + expCost value) (by
        simp_all [CodeCost, straight, charge, List.all_append, List.sum_append])
    exact ⟨shape.1, Nat.le_of_eq shape.2⟩
  | storeByte address value =>
    have first := expressionCost context (context.vmax + 1) live address
    rcases run1 : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨code1, value1, tmp1, live1⟩
    have second := expressionCost context tmp1 live1 value
    rcases run2 : compileExpHOLExact context tmp1 live1 value with
      ⟨code2, value2, tmp2, live2⟩
    simp only [compileHOLExact, run1, run2]
    have shape := nestedSeqCost (width := width) (code1 ++ code2 ++ [.assign tmp2 value1, .assign (tmp2 + 1) value2, .storeByte tmp2 (tmp2 + 1)])
      (expCost address + expCost value) (by
        simp_all [CodeCost, straight, charge, List.all_append, List.sum_append])
    exact ⟨shape.1, Nat.le_of_eq shape.2⟩
  | assign name value =>
    cases found : context.vars.lookup name with
    | none => simp [compileHOLExact, found, straight, charge]
    | some mapped =>
      have expr := expressionCost context (context.vmax + 1) live value
      rcases run : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, value1, tmp, outLive⟩
      have checked : CodeCost (code ++ [.assign mapped value1]) (expCost value) := by
        simp_all [CodeCost, straight, charge, List.all_append, List.sum_append]
      have shape := nestedSeqCost _ _ checked
      simpa [compileHOLExact, found, run, cost] using And.intro shape.1 (Nat.le_of_eq shape.2)
  | shMem operator name value =>
    cases found : context.vars.lookup name with
    | none => simp [compileHOLExact, found, straight, charge]
    | some mapped =>
      have expr := expressionCost context (context.vmax + 1) live value
      rcases run : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, value1, tmp, outLive⟩
      have checked : CodeCost (code ++ [.shMem operator mapped value1]) (expCost value) := by
        simp_all [CodeCost, straight, charge, List.all_append, List.sum_append]
      have shape := nestedSeqCost _ _ checked
      simpa [compileHOLExact, found, run, cost] using And.intro shape.1 (Nat.le_of_eq shape.2)
  | storeGlob address value =>
    have expr := expressionCost context (context.vmax + 1) live value
    rcases run : compileExpHOLExact context (context.vmax + 1) live value with
      ⟨code, value1, tmp, outLive⟩
    have checked : CodeCost (code ++ [.setGlobal address value1]) (expCost value) := by
      simp_all [CodeCost, straight, charge, List.all_append, List.sum_append]
    have shape := nestedSeqCost _ _ checked
    simpa [compileHOLExact, run, cost] using And.intro shape.1 (Nat.le_of_eq shape.2)
  | primitive destinations operator arguments =>
    simp only [compileHOLExact]
    split <;> simp [straight, charge, cost]
  | extCall function configuration configurationLength array arrayLength =>
    simp only [compileHOLExact]
    split <;> simp [straight, charge, cost]

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.leafCost

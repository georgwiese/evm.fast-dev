import InitECandidate.Solver.GasBudget.DispatchProgram

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Syntax.canSkip : Syntax → Bool
  | .action .skip => true
  | .action _ => false
  | .branch _ yes no => yes.canSkip || no.canSkip
  | .seq first second => first.canSkip && second.canSkip

def Syntax.canReturn : Syntax → Bool
  | .action .returned => true
  | .action _ => false
  | .branch _ yes no => yes.canReturn || no.canReturn
  | .seq first second => first.canReturn || (first.canSkip && second.canReturn)

theorem Syntax.choose_skip (tree : Syntax) (op : BitVec 64) : tree.choose op = .skip → tree.canSkip = true := by
  induction tree with
  | action leaf => cases leaf <;> simp [Syntax.choose, Syntax.canSkip]
  | branch guard yes no yesIH noIH =>
    intro chosen
    cases test : guard.test op with
    | false =>
      have h := noIH (by simpa [Syntax.choose, test] using chosen)
      simp [Syntax.canSkip, h]
    | true =>
      have h := yesIH (by simpa [Syntax.choose, test] using chosen)
      simp [Syntax.canSkip, h]
  | seq first second firstIH secondIH =>
    intro chosen
    cases selected : first.choose op with
    | skip =>
      have h₁ := firstIH (by simp only [selected])
      have h₂ := secondIH (by simpa [Syntax.choose, selected] using chosen)
      simp [Syntax.canSkip, h₁, h₂]
    | returned => simp [Syntax.choose, selected] at chosen
    | failed => simp [Syntax.choose, selected] at chosen
    | invoke function arguments => simp [Syntax.choose, selected] at chosen

theorem Syntax.choose_returned (tree : Syntax) (op : BitVec 64) : tree.choose op = .returned → tree.canReturn = true := by
  induction tree with
  | action leaf => cases leaf <;> simp [Syntax.choose, Syntax.canReturn]
  | branch guard yes no yesIH noIH =>
    intro chosen
    cases test : guard.test op with
    | false =>
      have h := noIH (by simpa [Syntax.choose, test] using chosen)
      simp [Syntax.canReturn, h]
    | true =>
      have h := yesIH (by simpa [Syntax.choose, test] using chosen)
      simp [Syntax.canReturn, h]
  | seq first second firstIH secondIH =>
    intro chosen
    cases selected : first.choose op with
    | skip =>
      have h₁ := first.choose_skip op selected
      have h₂ := secondIH (by simpa [Syntax.choose, selected] using chosen)
      simp [Syntax.canReturn, h₁, h₂]
    | returned =>
      have h := firstIH (by simp only [selected])
      simp [Syntax.canReturn, h]
    | failed => simp [Syntax.choose, selected] at chosen
    | invoke function arguments => simp [Syntax.choose, selected] at chosen

theorem no_skip : tree.canSkip = false := by decide
theorem no_direct_return : tree.canReturn = false := by decide

/-- Every original dispatcher choice is an actual opcode call followed by
its return, or the original invalid-opcode exception; no fallthrough or
unexplained direct success is assumed. This covers every64-bit opcode word. -/
theorem selection_cases (op : BitVec 64) :
    tree.choose op = .failed ∨ ∃ function arguments, tree.choose op = .invoke function arguments := by
  cases selected : tree.choose op with
  | skip =>
    have possible := tree.choose_skip op selected
    rw [no_skip] at possible
    cases possible
  | returned =>
    have possible := tree.choose_returned op selected
    rw [no_direct_return] at possible
    cases possible
  | failed => exact Or.inl rfl
  | invoke function arguments => exact Or.inr ⟨function, arguments, rfl⟩

theorem evaluation_cases (source : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op))) :
    (evaluateHOLFiniteState source body = evaluateHOLFiniteState source (.raise (ofString "EvmErr") (.const 5#64))) ∨
      (∃ function arguments, tree.choose op = .invoke function arguments ∧
        evaluateHOLFiniteState source body = evaluateHOLFiniteState source
          (.seq (.call (some (none, none)) (ofString function) arguments) (.return (.const 0#64)))) := by
  rcases selection_cases op with failed | ⟨function, arguments, selected⟩
  · left
    rw [body_choice source op opLocal, failed]
    rfl
  · right
    refine ⟨function, arguments, selected, ?_⟩
    rw [body_choice source op opLocal, selected]
    rfl

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.Syntax.choose_skip
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.Syntax.choose_returned
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.no_skip
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.no_direct_return
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_cases
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.evaluation_cases

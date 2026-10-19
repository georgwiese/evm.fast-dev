import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- A real early-return guard either produced that return in the incoming
state or skipped directly to the actual suffix. No successful test is assumed. -/
theorem return_guard_normal {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (test expression : ExpHOL 64) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (.return expression) .skip) continuation) =
      (some (.returned value), post)) :
    (eval source expression = some value ∧ post = emptyLocalsHOLFinite source) ∨
      evaluateHOLFiniteState source continuation = (some (.returned value), post) := by
  classical
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 F _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = result at normal
  cases result with
  | none => cases normal
  | some result =>
    cases result with
    | rStruct fields => cases normal
    | nStruct name fields => cases normal
    | val payload =>
      cases payload with
      | word word =>
        simp only at normal
        by_cases zero : word = 0
        · rw [if_pos zero, evaluateHOLFiniteState_skip] at normal
          exact Or.inr normal
        · rw [if_neg zero, evaluateHOLFiniteState_return] at normal
          cases read : evalHOLExact source.toExact expression with
          | none => simp only [read] at normal; cases normal
          | some returned =>
            by_cases small : sizeOfShapeWithContextHOL source.structs (shapeOfHOLExact returned) ≤ 32
            · simp only [read, if_pos small] at normal
              have resultEq := congrArg Prod.fst normal
              have valueEq : returned = value := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
              subst returned
              exact Or.inl ⟨read, (congrArg Prod.snd normal).symm⟩
            · simp only [read, if_neg small] at normal
              cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.return_guard_normal

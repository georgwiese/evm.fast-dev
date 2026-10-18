import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem return_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.return expression) = (some (.returned value), post)) :
    eval source expression = some value ∧ post = emptyLocalsHOLFinite source := by
  classical
  rw [evaluateHOLFiniteState_return] at normal
  split at normal
  · cases normal
  · rename_i actual read
    split at normal
    · have resultEq := congrArg Prod.fst normal
      have valueEq : actual = value := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
      exact ⟨read.trans (congrArg some valueEq), (congrArg Prod.snd normal).symm⟩
    · cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.return_normal

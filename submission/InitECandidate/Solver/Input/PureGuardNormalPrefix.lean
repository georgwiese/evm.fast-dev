import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem PureGuard.normal_prefix {F : Type} {program : ProgHOL 64} (guard : PureGuard program)
    (source post : PanSemStateFiniteExact 64 F) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq program continuation) = (some (.returned value), post)) :
    evaluateHOLFiniteState source program = (none, source) ∧
      evaluateHOLFiniteState source continuation = (some (.returned value), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at normal
  have info := guard.summary source
  generalize computed : evaluateHOLFiniteState source program = output at info normal ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have same := info.1 rfl
    change middle = source at same
    subst middle
    exact ⟨rfl, normal⟩
  | some result => exact (info.2 value (congrArg Prod.fst normal)).elim

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PureGuard.normal_prefix

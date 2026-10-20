import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine normal ignored ordinary call reinstalls each actual saved
caller local. Its callee need not satisfy any future-success contract. -/
theorem ignored_lookup {F : Type} (source post : PanSemStateFiniteExact 64 F) (key function : MlS) (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : post.locals.lookup key=source.locals.lookup key := by
  have safe : LocalPrefix key (.call (some (none,none)) function arguments) := .call none _ _ (by intro name impossible; cases impossible)
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [run] at summary
  exact summary.1 rfl

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_lookup

import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real counter loop of ignored calls and a local increment preserves
every other caller binding, irrespective of the callees' internal scopes. -/
theorem counter_loop_local {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (function : MlS) (arguments : List (ExpHOL 64)) (counter : String) (increment : ExpHOL 64)
    (key : MlS) (different : key ≠ ofString counter)
    (normal : evaluateHOLFiniteState source (.while condition (.seq (.call (some (none, none)) function arguments) (.assign .local (ofString counter) increment))) = (none, target)) :
    target.locals.lookup key = source.locals.lookup key := by
  have safe : LocalPrefix key (.while condition (.seq (.call (some (none, none)) function arguments) (.assign .local (ofString counter) increment))) :=
    .loop condition (.seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different))
  have summary := safe.summary source
  rw [normal] at summary
  exact summary.1 rfl

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.counter_loop_local

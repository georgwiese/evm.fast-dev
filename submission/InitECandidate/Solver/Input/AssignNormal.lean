import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal local assignment determines its complete state update.
The existing binding and shape check need not be assumed separately. -/
theorem assign_none {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (value : BitVec 64)
    (read : eval source expression = some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.assign .local (ofString name) expression) = (none, target)) :
    target = bind source name value := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign, read] at normal
  simp only at normal
  split at normal
  · have same := congrArg Prod.snd normal
    exact same.symm
  · cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.assign_none

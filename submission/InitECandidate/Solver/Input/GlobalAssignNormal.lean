import InitECandidate.Solver.Input.GlobalAssign

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal global assignment derives the actual full update without
an old-value or shape-check premise. -/
theorem global_assign_none {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (value : BitVec 64)
    (read : eval source expression = some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.assign .global (ofString name) expression) = (none, target)) :
    target = putGlobal source name value := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign, read] at normal
  simp only at normal
  split at normal
  · exact (congrArg Prod.snd normal).symm
  · cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.global_assign_none

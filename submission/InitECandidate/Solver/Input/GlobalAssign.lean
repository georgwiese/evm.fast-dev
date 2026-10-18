import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def putGlobal {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (word : BitVec 64) : PanSemStateFiniteExact 64 F :=
  {source with globals := source.globals.update (ofString name, .val (.word word))}

/-- Existing scalar globals accept an actual scalar expression read. -/
theorem global_assign_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (old word : BitVec 64)
    (expression : ExpHOL 64)
    (present : source.globals.lookup (ofString name) = some (.val (.word old)))
    (read : eval source expression = some (.val (.word word))) :
    evaluateHOLFiniteState source (.assign .global (ofString name) expression) = (none, putGlobal source name word) := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign, read]
  simp [isValidValueHOLFinite, lookupKvarHOLFinite, present, shapeOfHOLExact, shapeEqHOL,
    setKvarHOLFinite, setGlobalHOLFinite, putGlobal]

theorem putGlobal.lookup_same {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (word : BitVec 64) :
    (putGlobal source name word).globals.lookup (ofString name) = some (.val (.word word)) := by
  simp [putGlobal, HolFiniteMapExact.update, FUPDATE]

theorem putGlobal.lookup_other {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (word : BitVec 64) (key : MlS)
    (different : key ≠ ofString name) :
    (putGlobal source name word).globals.lookup key = source.globals.lookup key := by
  simp [putGlobal, HolFiniteMapExact.update, FUPDATE, Ne.symm different]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.global_assign_execute
#print axioms InitECandidate.Solver.Input.putGlobal.lookup_same
#print axioms InitECandidate.Solver.Input.putGlobal.lookup_other

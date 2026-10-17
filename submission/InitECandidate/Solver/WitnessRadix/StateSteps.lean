import InitECandidate.Solver.WitnessRadix.QueryBranchStep

namespace InitECandidate.Solver.WitnessRadix.StateSteps
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem fixed_clock {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (result : Option (PanSemResultExact 64)) (clock : target.clock ≤ source.clock) :
    fixClockHOLFinite source (result, target) = (result, target) := by
  have notGreater : ¬ source.clock < target.clock := by omega
  simp [fixClockHOLFinite, notGreater]

theorem next_sequence {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (run : evaluateHOLFiniteState source first = (none, target))
    (clock : target.clock ≤ source.clock) :
    evaluateHOLFiniteState source (.seq first second) = evaluateHOLFiniteState target second := by
  rw [evaluateHOLFiniteState_seq, run]
  simp only [fixed_clock source target none clock]

theorem stopped_sequence {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (result : PanSemResultExact 64)
    (run : evaluateHOLFiniteState source first = (some result, target))
    (clock : target.clock ≤ source.clock) :
    evaluateHOLFiniteState source (.seq first second) = (some result, target) := by
  rw [evaluateHOLFiniteState_seq, run]
  simp only [fixed_clock source target (some result) clock]

theorem assign_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (old new : BitVec 64)
    (present : source.locals.lookup (ofString name) = some (.val (.word old)))
    (read : eval source expression = some (.val (.word new))) :
    evaluateHOLFiniteState source (.assign .local (ofString name) expression) = (none, bind source name new) := by
  classical
  have valid : isValidValueHOLFinite source .local (ofString name) (.val (.word new)) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, present, shapeOfHOLExact, shapeEqHOL]
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign, read]
  simp only [← isValidValueHOLFinite_eq, valid, ↓reduceIte, setKvarHOLFinite]
  rfl

end InitECandidate.Solver.WitnessRadix.StateSteps

#print axioms InitECandidate.Solver.WitnessRadix.StateSteps.assign_execute

import InitECandidate.Solver.Input.HeaderGuards
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actual returning enclosing run rules out a decoder rejection without
an extra minimum-clock premise. Checked clock extension is used only to show
the rejection impossible; the passing continuation uses the original state. -/
theorem guard_actual (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (condition : ExpHOL 64) (error : BitVec 64) (bad : Prop) [Decidable bad]
    (read : eval source condition = some (.val (.word (if bad then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source
      (.seq (.ite condition (.call (some (none, none)) (ofString "ssz_fail") [.const error]) .skip) continuation) =
      (some (.returned value), target)) :
    ¬ bad ∧ evaluateHOLFiniteState source continuation = (some (.returned value), target) := by
  classical
  let guard : ProgHOL 64 := .ite condition (.call (some (none, none)) (ofString "ssz_fail") [.const error]) .skip
  by_cases rejected : bad
  · let padded := {source with clock := source.clock + 1}
    have paddedRead : eval padded condition = some (.val (.word (if bad then 1#64 else 0#64))) := by
      change evalHOLExact (stateAddClock source.toExact 1) condition = _
      rw [evalHOLExact_stateAddClock]
      exact read
    have stopped := Header.test_guard_execute padded condition error bad paddedRead code shape (by dsimp [padded]; omega)
    rw [if_pos rejected] at stopped
    have larger := panPropsEvaluateAddClockEq (.seq guard continuation) source (some (.returned value)) target 1 ⟨actual, by simp⟩
    rw [evaluateHOLFiniteState_seq_line780, stopped] at larger
    cases congrArg Prod.fst larger
  · have passed : evaluateHOLFiniteState source guard = (none, source) := by
      change @evalHOLExact 64 Guest.HostMemory _ source.toExact _ condition = _ at read
      change evaluateHOLFiniteState source (.ite condition (.call (some (none, none)) (ofString "ssz_fail") [.const error]) .skip) = _
      rw [evaluateHOLFiniteState_ite, read, if_neg rejected]
      simp
    exact ⟨rejected, (WitnessRadix.StateSteps.next_sequence source source guard continuation passed (Nat.le_refl _)).symm.trans actual⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.guard_actual

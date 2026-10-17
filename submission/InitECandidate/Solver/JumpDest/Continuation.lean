import InitECandidate.Solver.JumpDest.Reads
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem bind_overwrite {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (first second : BitVec 64) :
    WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source name first) name second =
      WitnessRadix.QueryBranch.bind source name second := by
  unfold WitnessRadix.QueryBranch.bind setVarHOLFinite
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  by_cases same : ofString name = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]

theorem next_bind {F : Type} (source : PanSemStateFiniteExact 64 F) (word : BitVec 64) :
    eval (WitnessRadix.QueryBranch.bind source "adv" word) nextByte = eval source nextByte := by
  simp [eval, nextByte, localVar, evalHOLExact, evalListHOLExact, toExact,
    WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  rfl

noncomputable def continuationWord (index length next low : BitVec 64) : BitVec 64 := by
  classical
  exact if index + 1#64 < length ∧ ¬ next < low ∧ ¬ 127#64 < next then 1#64 else 2#64

/-- Actual continuation-byte branch: its only effect is a one/two-byte
advance. The optional byte read is required only on the real in-range path;
all local shadowing/restoration is included. -/
theorem continuation_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (low index length next old : BitVec 64)
    (different : ofString name ≠ ofString "adv")
    (advLocal : source.locals.lookup (ofString "adv") = some (.val (.word old)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (loaded : index + 1#64 < length → eval source nextByte = some (.val (.word next))) :
    evaluateHOLFiniteState source (continuationAdvance name low) =
      (none, WitnessRadix.QueryBranch.bind source "adv" (continuationWord index length next low)) := by
  classical
  let stage := WitnessRadix.QueryBranch.bind source "adv" 2#64
  have setTwo := WitnessRadix.StateSteps.assign_execute source "adv" (.const 2#64) old 2#64 advLocal rfl
  have pcStage : stage.locals.lookup (ofString "pc") = some (.val (.word index)) :=
    (bind_lookup_other source "adv" "pc" _ (by decide)).trans pcLocal
  have nStage : stage.locals.lookup (ofString "n") = some (.val (.word length)) :=
    (bind_lookup_other source "adv" "n" _ (by decide)).trans nLocal
  have test := next_test_read stage index length pcStage nStage
  simp only [eval] at test
  rw [continuationAdvance, setAdvance,
    WitnessRadix.StateSteps.next_sequence source stage _ _ setTwo (Nat.le_refl _), evaluateHOLFiniteState_ite, test]
  by_cases following : index + 1#64 < length
  · simp only [flag, if_pos following, if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)]
    have readNext : eval stage nextByte = some (.val (.word next)) := by
      rw [next_bind]
      exact loaded following
    let inner := WitnessRadix.QueryBranch.bind stage name next
    have innerNext : inner.locals.lookup (ofString name) = some (.val (.word next)) := bind_lookup_same _ _ _
    have innerAdv : inner.locals.lookup (ofString "adv") = some (.val (.word 2#64)) :=
      (bind_lookup_other stage name "adv" next different).trans (bind_lookup_same _ _ _)
    have rangeTest := range_read inner name next low 127#64 innerNext
    simp only [eval] at rangeTest
    by_cases accepted : ¬ next < low ∧ ¬ 127#64 < next
    · have setOne := WitnessRadix.StateSteps.assign_execute inner "adv" (.const 1#64) 2#64 1#64 innerAdv rfl
      have branchRun : evaluateHOLFiniteState inner (.ite (inRange name low 127#64) (setAdvance 1#64) .skip) =
          (none, WitnessRadix.QueryBranch.bind inner "adv" 1#64) := by
        rw [evaluateHOLFiniteState_ite, rangeTest]
        simp only [flag, if_pos accepted, if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide), setAdvance]
        exact setOne
      have declared := Input.ScalarScope.declare_execute stage _ name nextByte next
        (.ite (inRange name low 127#64) (setAdvance 1#64) .skip) none readNext branchRun
      rw [restore_bind_other stage inner name "adv" 1#64 different, restore_bound stage name next,
        bind_overwrite source "adv" 2#64 1#64] at declared
      simpa only [continuationWord, if_pos (And.intro following accepted)] using declared
    · have branchRun : evaluateHOLFiniteState inner (.ite (inRange name low 127#64) (setAdvance 1#64) .skip) = (none, inner) := by
        rw [evaluateHOLFiniteState_ite, rangeTest]
        simp only [flag, if_neg accepted]
        simp [evaluateHOLFiniteState_skip]
      have declared := Input.ScalarScope.declare_execute stage _ name nextByte next
        (.ite (inRange name low 127#64) (setAdvance 1#64) .skip) none readNext branchRun
      rw [restore_bound stage name next] at declared
      simpa only [continuationWord, if_neg (show ¬ (index + 1#64 < length ∧ ¬ next < low ∧ ¬ 127#64 < next) from fun h => accepted h.2)] using declared
  · simp [flag, following, continuationWord, evaluateHOLFiniteState_skip, stage]

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.bind_overwrite
#print axioms InitECandidate.Solver.JumpDest.next_bind
#print axioms InitECandidate.Solver.JumpDest.continuation_execute

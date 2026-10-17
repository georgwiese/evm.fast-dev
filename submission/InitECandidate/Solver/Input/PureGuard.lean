import InitECandidate.Solver.PanState
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Read-only validation branches: they can continue or fail, but cannot
write state, call another routine, or return a caller's result. -/
inductive PureGuard : ProgHOL 64 → Prop where
  | skip : PureGuard .skip
  | raise (name : MlS) (expression : ExpHOL 64) : PureGuard (.raise name expression)
  | ite (test : ExpHOL 64) {left right : ProgHOL 64}
      (leftGuard : PureGuard left) (rightGuard : PureGuard right) : PureGuard (.ite test left right)
  | seq {left right : ProgHOL 64} (leftGuard : PureGuard left) (rightGuard : PureGuard right) :
      PureGuard (.seq left right)

theorem PureGuard.summary {F : Type} {program : ProgHOL 64} (guard : PureGuard program)
    (source : PanSemStateFiniteExact 64 F) :
    ((evaluateHOLFiniteState source program).1 = none → (evaluateHOLFiniteState source program).2 = source) ∧
      ∀ value, (evaluateHOLFiniteState source program).1 ≠ some (.returned value) := by
  classical
  induction guard generalizing source with
  | skip => simp [evaluateHOLFiniteState_skip]
  | raise name expression =>
    rw [evaluateHOLFiniteState_raise]
    split <;> simp_all
    all_goals split <;> simp_all
  | ite test leftGuard rightGuard leftIH rightIH =>
    rw [evaluateHOLFiniteState_ite]
    generalize read : @evalHOLExact 64 F _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) test = observed
    cases observed with
    | none => simp
    | some value =>
      cases value with
      | val payload =>
        cases payload with
        | word word =>
          by_cases zero : word = 0
          · simpa only [if_pos zero] using rightIH source
          · simpa only [if_neg zero] using leftIH source
      | rStruct fields => simp
      | nStruct name fields => simp
  | seq leftGuard rightGuard leftIH rightIH =>
    rw [evaluateHOLFiniteState_seq_line780]
    have first := leftIH source
    generalize computed : evaluateHOLFiniteState source _ = output at first ⊢
    obtain ⟨result, middle⟩ := output
    cases result with
    | none =>
      have same := first.1 rfl
      change middle = source at same
      subst middle
      exact rightIH source
    | some result =>
      constructor
      · intro impossible
        cases impossible
      · exact first.2

/-- Inverting a genuine normal return skips any earlier read-only guards
without assuming their reads, conditions, or exception metadata are valid. -/
theorem PureGuard.normal_continue {F : Type} {program : ProgHOL 64} (guard : PureGuard program)
    (source post : PanSemStateFiniteExact 64 F) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq program continuation) = (some (.returned value), post)) :
    evaluateHOLFiniteState source continuation = (some (.returned value), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  have info := guard.summary source
  generalize computed : evaluateHOLFiniteState source program = output at info run
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have same := info.1 rfl
    change middle = source at same
    subst middle
    exact run
  | some result =>
    exact False.elim (info.2 value (congrArg Prod.fst run))

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PureGuard.summary
#print axioms InitECandidate.Solver.Input.PureGuard.normal_continue

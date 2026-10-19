import InitECandidate.Solver.Input.ReturnGuardNormal
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ExceptionControl
import InitECandidate.Solver.Input.NoException

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem return_guard_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test expression : ExpHOL 64)
    (normal : evaluateHOLFiniteState source (.ite test (.return expression) .skip) = (none, post)) : post = source := by
  classical
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = result at normal
  cases result with
  | none => cases normal
  | some result =>
    cases result with
    | rStruct fields => cases normal
    | nStruct name fields => cases normal
    | val payload =>
      cases payload with
      | word word =>
        simp only at normal
        by_cases zero : word = 0
        · rw [if_pos zero, evaluateHOLFiniteState_skip] at normal
          exact (congrArg Prod.snd normal).symm
        · rw [if_neg zero] at normal
          exact ((NoFallthrough.returned expression) source (congrArg Prod.fst normal)).elim

/-- Escaping exceptions follow the real skipped early-return guard and
therefore execute the suffix in exactly the same incoming state. -/
theorem return_guard_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test expression : ExpHOL 64) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (.return expression) .skip) continuation) =
      (some (.exception identifier payload), post)) :
    evaluateHOLFiniteState source continuation = (some (.exception identifier payload), post) := by
  rcases sequence_exception source post (.ite test (.return expression) .skip) continuation identifier payload normal with failed | continued
  · have safe := NoException.conditional source.code test (.return expression) .skip
      (NoException.returned source.code expression) (NoException.skip source.code)
    exact (safe source rfl identifier payload (congrArg Prod.fst failed)).elim
  · obtain ⟨middle, guardRun, tailRun⟩ := continued
    have same := return_guard_none source middle test expression guardRun
    subst middle
    exact tailRun

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.return_guard_none
#print axioms InitECandidate.Solver.Input.return_guard_exception

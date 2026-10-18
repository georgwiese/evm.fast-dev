import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Actual normal continuation proves that its preceding read-only guard
really passed, rather than merely supplying a hypothetical suffix run. -/
theorem PureGuard.normal_passed {F : Type} {program : ProgHOL 64} (guard : PureGuard program)
    (source post : PanSemStateFiniteExact 64 F) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq program continuation) = (some (.returned value), post)) :
    evaluateHOLFiniteState source program = (none, source) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  have info := guard.summary source
  generalize computed : evaluateHOLFiniteState source program = output at info run
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have same : middle = source := info.1 rfl
    subst middle
    rfl
  | some result => exact False.elim (info.2 value (congrArg Prod.fst run))

/-- Raising cannot fall through even if its expression or exception shape
is invalid: those failures produce an error instead of a normal outcome. -/
theorem raise_ne_none {F : Type} (source : PanSemStateFiniteExact 64 F) (name : MlS) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState source (.raise name expression)).1 ≠ none := by
  classical
  rw [evaluateHOLFiniteState_raise]
  cases shape : source.eshapes.lookup name with
  | none => simp
  | some shape =>
    cases read : @evalHOLExact 64 F _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address)) expression with
    | none => simp
    | some value =>
      dsimp only
      split <;> simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PureGuard.normal_passed
#print axioms InitECandidate.Solver.Input.raise_ne_none

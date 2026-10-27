import InitECandidate.Solver.Input.NoneControl
import Guest.Model

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def NoFallthrough (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, (evaluateHOLFiniteState source program).1 ≠ none

theorem NoFallthrough.returned (expression : ExpHOL 64) : NoFallthrough (.return expression) := by
  intro source
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem NoFallthrough.sequence (first second : ProgHOL 64) (tail : NoFallthrough second) : NoFallthrough (.seq first second) := by
  intro source normal
  have run : evaluateHOLFiniteState source (.seq first second) = (none, (evaluateHOLFiniteState source (.seq first second)).2) := Prod.ext normal rfl
  obtain ⟨middle, firstRun, secondRun⟩ := sequence_none source _ first second run
  exact tail middle (congrArg Prod.fst secondRun)

theorem NoFallthrough.declared (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (tail : NoFallthrough body) : NoFallthrough (.dec name shape expression body) := by
  intro source
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · split
    · exact tail _
    · simp

theorem NoFallthrough.scoped (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (tail : NoFallthrough continuation) : NoFallthrough (.decCall name shape function arguments continuation) := by
  classical
  intro source
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; simp
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; simp
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · simp [zero]
      · rw [if_neg zero]
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output
        obtain ⟨result, target⟩ := output
        cases result with
        | none => simp
        | some result =>
          cases result with
          | returned returned =>
            simp only
            split
            · exact tail _
            · simp
          | error => simp
          | timeOut => simp
          | «break» => simp
          | «continue» => simp
          | exception identifier payload => simp
          | finalFfi event => simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.NoFallthrough.returned
#print axioms InitECandidate.Solver.Input.NoFallthrough.sequence
#print axioms InitECandidate.Solver.Input.NoFallthrough.declared
#print axioms InitECandidate.Solver.Input.NoFallthrough.scoped

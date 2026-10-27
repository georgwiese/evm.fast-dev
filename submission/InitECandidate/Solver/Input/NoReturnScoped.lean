import InitECandidate.Solver.Input.NoReturnIgnored
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem store (address value : ExpHOL 64) : Never (.store address value) := by
  intro F source returned
  have safe : LocalPrefix (ofString "_") (.store address value) := .store _ _
  exact (safe.summary source).2 returned

theorem raised_sequence (name : MlS) (expression : ExpHOL 64) (continuation : ProgHOL 64) :
    Never (.seq (.raise name expression) continuation) := by
  intro F source value
  have stops : (evaluateHOLFiniteState source (.raise name expression)).1 ≠ none := by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> simp
    · simp
  have notReturn := NoReturn.raise name expression source value
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source (.raise name expression) = output at stops notReturn ⊢
  obtain ⟨result, target⟩ := output
  cases result with
  | none => exact (stops rfl).elim
  | some result => exact notReturn

theorem scoped_call (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (tail : Never continuation) : Never (.decCall name shape function arguments continuation) := by
  classical
  intro F source value
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
            · exact tail _ value
            · simp
          | error => simp
          | timeOut => simp
          | «break» => simp
          | «continue» => simp
          | exception identifier payload => simp
          | finalFfi event => simp

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.store
#print axioms InitECandidate.Solver.Input.NoReturn.raised_sequence
#print axioms InitECandidate.Solver.Input.NoReturn.scoped_call

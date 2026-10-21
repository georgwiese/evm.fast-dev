import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A scoped callee cannot export its own break/continue. The caller can
produce those only through its genuine continuation. -/
theorem scoped_no_loop_control (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      (evaluateHOLFiniteState source continuation).1≠some .break ∧ (evaluateHOLFiniteState source continuation).1≠some .continue)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source (.decCall name shape function arguments continuation)).1≠some .break ∧
      (evaluateHOLFiniteState source (.decCall name shape function arguments continuation)).1≠some .continue := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments with
  | none=>simp only [args]; simp
  | some values=>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>simp only [called]; simp
    | some data=>
      obtain ⟨body,callee,returnShape⟩ := data
      simp only [called]
      by_cases zero : source.clock=0
      · rw [if_pos zero]
        simp
      · rw [if_neg zero]
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output
        obtain ⟨result,target⟩ := output
        cases result with
        | none=>simp
        | some result=>
          cases result with
          | returned value=>
            simp only
            split
            · exact safe _
            · simp
          | error=>simp
          | timeOut=>simp
          | «break»=>simp
          | «continue»=>simp
          | exception name value=>simp
          | finalFfi event=>simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.scoped_no_loop_control

import InitECandidate.Solver.Input.NormalCallEntry

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Any normal return through a scoped call proves that its call clock was
available, regardless of argument or code lookup failures. -/
theorem normal_clock {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall name shape function arguments continuation) =
      (some (.returned value), post)) : 1 ≤ source.clock := by
  classical
  by_contra insufficient
  have zero : source.clock = 0 := by omega
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
  cases args : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at run; cases run
  | some values =>
    simp only [args] at run
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at run; cases run
    | some entry =>
      obtain ⟨body, callee, returnShape⟩ := entry
      simp only [called, if_pos zero] at run
      cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.normal_clock

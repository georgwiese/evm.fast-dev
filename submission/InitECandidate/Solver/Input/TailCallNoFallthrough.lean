import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real tail call always returns control or stops; it cannot resume a
following caller statement, including on argument, clock or shape failure. -/
theorem NoFallthrough.tail_call (function : MlS) (arguments : List (ExpHOL 64)) : NoFallthrough (.call none function arguments) := by
  classical
  intro source
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments with
  | none=>simp only; simp
  | some values=>
    simp only
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>simp only; simp
    | some triple=>
      obtain ⟨body,callee,shape⟩:=triple
      simp only
      by_cases zero : source.clock=0
      · simp [zero]
      · rw [if_neg zero]
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output
        obtain ⟨result,target⟩:=output
        cases result with
        | none=>simp
        | some result=>
          cases result <;> simp
          all_goals split <;> simp

/-- A caller suffix after a non-falling-through program is unreachable. -/
theorem NoFallthrough.sequence_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (terminal : NoFallthrough first) : evaluateHOLFiniteState source (.seq first second)=evaluateHOLFiniteState source first := by
  have never:=terminal source
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at never ⊢
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>exact (never rfl).elim
  | some result=>rfl

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.NoFallthrough.tail_call
#print axioms InitECandidate.Solver.Input.NoFallthrough.sequence_eq

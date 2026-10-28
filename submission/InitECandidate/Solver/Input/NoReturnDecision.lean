import InitECandidate.Solver.Input.NoReturnAtoms

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem breaks : Never (.break : ProgHOL 64) := by
  intro F source value
  simp [evaluateHOLFiniteState_break]

/-- A finite conditional whose branches cannot return also cannot return,
including failed guard reads and nonscalar guard values. -/
theorem conditional (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Never yes) (right : Never no) : Never (.ite test yes no) := by
  intro F source returned
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 F _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=value
  cases value with
  | none=>simp
  | some value=>
    cases value with
    | rStruct fields=>simp
    | nStruct name fields=>simp
    | val payload=>
      cases payload with
      | word word=>
        simp only
        by_cases zero : word=0
        · rw [if_pos zero]
          exact right source returned
        · rw [if_neg zero]
          exact left source returned

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.breaks
#print axioms InitECandidate.Solver.Input.NoReturn.conditional

import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuinely normally continuing conditional ran one of its actual
branches normally. Failed or nonscalar condition reads cannot be supplied
as a normal branch execution. -/
theorem conditional_none {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (test : ExpHOL 64) (yes no : ProgHOL 64)
    (normal : evaluateHOLFiniteState source (.ite test yes no)=(none,post)) :
    evaluateHOLFiniteState source yes=(none,post) ∨ evaluateHOLFiniteState source no=(none,post) := by
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 F _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=value at normal
  cases value with
  | none=>simp at normal
  | some value=>
    cases value with
    | rStruct fields=>simp at normal
    | nStruct name fields=>simp at normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero] at normal
          exact Or.inr normal
        · rw [if_neg zero] at normal
          exact Or.inl normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.conditional_none

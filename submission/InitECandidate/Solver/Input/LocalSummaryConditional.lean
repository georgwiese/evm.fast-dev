import InitECandidate.Solver.Input.LocalLoopSummary

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem local_summary_conditional {F : Type} (key : MlS) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : ∀ source : PanSemStateFiniteExact 64 F,LocalSummary key yes source)
    (right : ∀ source : PanSemStateFiniteExact 64 F,LocalSummary key no source)
    (source : PanSemStateFiniteExact 64 F) : LocalSummary key (.ite test yes no) source := by
  unfold LocalSummary
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 F _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) test=value
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
        · rw [if_pos zero]; exact right source
        · rw [if_neg zero]; exact left source

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.local_summary_conditional

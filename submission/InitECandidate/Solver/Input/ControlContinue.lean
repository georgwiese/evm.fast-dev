import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

inductive ControlResult : Option (PanSemResultExact 64) → Prop where
  | next : ControlResult none
  | returned (value : ValueHOL 64) : ControlResult (some (.returned value))
  | breaks : ControlResult (some .break)
  | continues : ControlResult (some .continue)

/-- A safe prefix must finish normally before an enclosing ordinary control
result. This also handles loop break/continue, rather than assuming them away
while extracting actual calls from a normal enclosing loop. -/
theorem LocalPrefix.control_continue {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalPrefix key program) (source post : PanSemStateFiniteExact 64 F)
    (continuation : ProgHOL 64) (result : Option (PanSemResultExact 64)) (control : ControlResult result)
    (run : evaluateHOLFiniteState source (.seq program continuation) = (result, post)) :
    ∃ middle, evaluateHOLFiniteState source program = (none, middle) ∧
      evaluateHOLFiniteState middle continuation = (result, post) ∧ middle.locals.lookup key = source.locals.lookup key := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  have info := safe.summary_full source
  unfold LocalSummary at info
  generalize computed : evaluateHOLFiniteState source program = output at info run
  obtain ⟨prefixResult, middle⟩ := output
  cases prefixResult with
  | none => exact ⟨middle, rfl, run, info.1 rfl⟩
  | some prefixResult =>
    have same := congrArg Prod.fst run
    change some prefixResult = result at same
    cases control with
    | next => cases same
    | returned value => exact (info.2.1 value same).elim
    | breaks => exact (info.2.2.1 same).elim
    | continues => exact (info.2.2.2 same).elim

theorem LocalPrefix.control_none {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalPrefix key program) (source target : PanSemStateFiniteExact 64 F)
    (result : Option (PanSemResultExact 64)) (control : ControlResult result)
    (run : evaluateHOLFiniteState source program = (result, target)) : result = none := by
  have info := safe.summary_full source
  unfold LocalSummary at info
  rw [run] at info
  cases control with
  | next => rfl
  | returned value => exact (info.2.1 value rfl).elim
  | breaks => exact (info.2.2.1 rfl).elim
  | continues => exact (info.2.2.2 rfl).elim

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.LocalPrefix.control_continue
#print axioms InitECandidate.Solver.Input.LocalPrefix.control_none

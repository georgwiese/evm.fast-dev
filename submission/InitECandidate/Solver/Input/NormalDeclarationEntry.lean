import InitECandidate.Solver.Input.NormalCallEntry

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal enclosing return derives successful expression evaluation and
shape checking at the actual declaration, and exposes its real inner run. -/
theorem declaration_normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.dec (ofString name) shape expression continuation) =
      (some (.returned value), post)) :
    ∃ declared inner, eval source expression = some declared ∧
      shapeEqHOL shape (shapeOfHOLExact declared) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation =
        (some (.returned value), inner) ∧ post = restore source name inner := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only at run
  cases read : eval source expression with
  | none =>
    simp only [eval] at read
    rw [read] at run
    cases run
  | some declared =>
    have actualRead := read
    simp only [eval] at actualRead
    rw [actualRead] at run
    simp only at run
    by_cases valid : shapeEqHOL shape (shapeOfHOLExact declared) = true
    · rw [if_pos valid] at run
      have resultEq := congrArg Prod.fst run
      have postEq := congrArg Prod.snd run
      refine ⟨declared, (evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation).2,
        rfl, valid, ?_, ?_⟩
      · exact Prod.ext resultEq rfl
      · exact postEq.symm
    · rw [if_neg valid] at run
      cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.declaration_normal_entry

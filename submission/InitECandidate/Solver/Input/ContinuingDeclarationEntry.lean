import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real continuing declaration derives its successful read and exact
inner execution. Its declared value may be arbitrary proof-independent data. -/
theorem declaration_continuing_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (run : evaluateHOLFiniteState source (.dec (ofString name) shape expression continuation)=(none,post)) :
    ∃ declared inner,eval source expression=some declared ∧ shapeEqHOL shape (shapeOfHOLExact declared)=true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation=(none,inner) ∧ post=restore source name inner := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only at run
  cases read : eval source expression with
  | none=>simp only [eval] at read; rw [read] at run; cases run
  | some declared=>
    have actualRead := read
    simp only [eval] at actualRead
    rw [actualRead] at run
    simp only at run
    by_cases valid : shapeEqHOL shape (shapeOfHOLExact declared)=true
    · rw [if_pos valid] at run
      have observed := congrArg Prod.fst run
      have endpoint := congrArg Prod.snd run
      exact ⟨declared,(evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation).2,rfl,valid,Prod.ext observed rfl,endpoint.symm⟩
    · rw [if_neg valid] at run; cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.declaration_continuing_entry

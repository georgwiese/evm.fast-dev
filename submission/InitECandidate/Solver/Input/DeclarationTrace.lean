import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual declaration either fails before spending a source tick or
exposes its real read/shape check, inner run and lexical restoration. The
initial value is arbitrary, including word labels permitted by scalar shape. -/
theorem declaration_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.dec (ofString name) shape expression continuation)=(outcome,post)) :
    source.clock-post.clock≤0 ∨ ∃ declared inner,eval source expression=some declared ∧
      shapeEqHOL shape (shapeOfHOLExact declared)=true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation=(outcome,inner) ∧ post=restore source name inner := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only at run
  cases read : eval source expression with
  | none=>
    simp only [eval] at read
    rw [read] at run
    have endpoint : post=source := (congrArg Prod.snd run).symm
    exact Or.inl (by rw [endpoint]; omega)
  | some declared=>
    have actualRead:=read
    simp only [eval] at actualRead
    rw [actualRead] at run
    simp only at run
    by_cases valid : shapeEqHOL shape (shapeOfHOLExact declared)=true
    · rw [if_pos valid] at run
      have observed:=congrArg Prod.fst run
      have endpoint:=congrArg Prod.snd run
      exact Or.inr ⟨declared,(evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) continuation).2,rfl,valid,Prod.ext observed rfl,endpoint.symm⟩
    · rw [if_neg valid] at run
      have endpoint : post=source := (congrArg Prod.snd run).symm
      exact Or.inl (by rw [endpoint]; omega)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.declaration_trace

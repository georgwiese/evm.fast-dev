import InitECandidate.Solver.Input.ScalarWordShape
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- Every successful ordinary word operation returns one scalar, regardless
of its argument reads. This derives the real store width from evaluation. -/
theorem operation_word_result {F : Type} (source : PanSemStateFiniteExact 64 F)
    (operator : BinOp) (arguments : List (ExpHOL 64)) (value : ValueHOL 64)
    (read : eval source (.op operator arguments)=some value) : ∃ word : BitVec 64,value=.val (.word word) := by
  classical
  simp only [eval,evalHOLExact] at read
  cases args : evalListHOLExact source.toExact arguments with
  | none=>simp [args] at read
  | some values=>
    simp only [args] at read
    split at read
    · cases computed : wordOpHOL operator (values.map valueWord) with
      | none=>simp [computed] at read
      | some word=>exact ⟨word,by simpa [computed] using read.symm⟩
    · cases read

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.operation_word_result

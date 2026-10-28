import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang

/-- The checked exact scalar carrier is an actual word. This fact needs no
integer arithmetic, serializer or guest-specific helper implementation. -/
theorem scalar_word_of_shape (value : ValueHOL 64) (shape : shapeOfHOLExact value=.one) :
    ∃ word : BitVec 64,value=.val (.word word) := by
  cases value with
  | val payload=>cases payload with | word word=>exact ⟨word,rfl⟩
  | rStruct fields=>simp only [shapeOfHOLExact] at shape; cases shape
  | nStruct name fields=>simp only [shapeOfHOLExact] at shape; cases shape

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.scalar_word_of_shape

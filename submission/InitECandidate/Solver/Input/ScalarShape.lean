import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace InitECandidate.Solver.Input.ScalarShape
open Flapjack Flapjack.Pancake.PanLang

/-- The actual source value carrier has word leaves. A checked scalar shape
therefore identifies an actual word, independently of serialization code. -/
theorem word (value : ValueHOL 64) (shape : shapeOfHOLExact value = .one) :
    ∃ word : BitVec 64, value = .val (.word word) := by
  cases value with
  | val payload => cases payload with | word word => exact ⟨word, rfl⟩
  | rStruct fields => simp only [shapeOfHOLExact] at shape; cases shape
  | nStruct name fields => simp only [shapeOfHOLExact] at shape; cases shape

end InitECandidate.Solver.Input.ScalarShape

#print axioms InitECandidate.Solver.Input.ScalarShape.word

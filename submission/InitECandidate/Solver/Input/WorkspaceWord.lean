import InitECandidate.Solver.Input.ScalarProgram

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Scalar workspace-word lookup, independent of the decoder's allocation
prefix. The historical namespace keeps existing callers compatible. -/
theorem word_read {F : Type} (source : PanSemStateFiniteExact 64 F) (array value : BitVec 64) (offset : Nat)
    (globalArray : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (mapped : source.memaddrs (array + BitVec.ofNat 64 offset))
    (cell : source.memory (array + BitVec.ofNat 64 offset) = .word value) :
    eval source (.load .one (Scalar.plus (.var .global (ofString "ssz_offs")) offset)) = some (.val (.word value)) := by
  classical
  have base : eval source (.var .global (ofString "ssz_offs")) = some (.val (.word array)) := by
    simpa [eval, evalHOLExact, toExact] using globalArray
  have address := Scalar.plus_read source (.var .global (ofString "ssz_offs")) array offset base
  simp only [eval] at address ⊢
  rw [evalHOLExact, address]
  simp [isWfShapeExactHOL, memLoadHOLExact, toExact, mapped, cell]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.word_read

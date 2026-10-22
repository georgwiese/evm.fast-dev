import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.ByteStoreLocal

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem skip : Never (.skip : ProgHOL 64) := by
  intro F source value
  simp [evaluateHOLFiniteState_skip]

theorem declared (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (tail : Never body) : Never (.dec name shape expression body) := by
  intro F source value
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · split
    · exact tail _ value
    · simp

theorem store_byte (address value : ExpHOL 64) : Never (.storeByte address value) := by
  intro F source returned
  exact (byte_store_local (Flapjack.Basis.Pure.MlString.ofString "_") address value source).2.1 returned

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.skip
#print axioms InitECandidate.Solver.Input.NoReturn.declared
#print axioms InitECandidate.Solver.Input.NoReturn.store_byte

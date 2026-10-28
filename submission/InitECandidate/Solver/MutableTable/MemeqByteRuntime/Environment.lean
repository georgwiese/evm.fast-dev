import InitECandidate.Solver.WitnessRadix.MemeqFormals
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def values (a b : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word a), .val (.word b), .val (.word (BitVec.ofNat 64 length))]
def rawLocals (a b : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 length))) else
  if name = ofString "b" then some (.val (.word b)) else
  if name = ofString "a" then some (.val (.word a)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (a b : BitVec 64) (length : Nat) (known : table (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "memeq") (values a b length) = some (Memeq32.body, callee, .one) ∧
      callee.lookup (ofString "a") = some (.val (.word a)) ∧ callee.lookup (ofString "b") = some (.val (.word b)) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (Memeq32.formals.map Prod.fst).Nodup ∧ Memeq32.formals.length = (values a b length).length ∧
      ((Memeq32.formals.zip (values a b length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [Memeq32.formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "memeq") (values a b length) = some (Memeq32.body, rawLocals a b length, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup table
    (ofString "memeq") (values a b length) Memeq32.body (rawLocals a b length) .one raw
  refine ⟨callee, called, ?_, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "a" ≠ ofString "b" from by decide, show ofString "a" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals, show ofString "b" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals]

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.environment

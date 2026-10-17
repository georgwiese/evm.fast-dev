import InitECandidate.Solver.JumpDest.Program
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "code", .one), (ofString "n", .one)]
def values (code length : BitVec 64) : List (ValueHOL 64) := [.val (.word code), .val (.word length)]
def rawLocals (code length : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word length)) else if name = ofString "code" then some (.val (.word code)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (code length : BitVec 64)
    (known : table (ofString "compute_jumpdests") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "compute_jumpdests") (values code length) = some (body, callee, .one) ∧
      callee.lookup (ofString "code") = some (.val (.word code)) ∧
      callee.lookup (ofString "n") = some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values code length).length ∧
      ((formals.zip (values code length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "compute_jumpdests") (values code length) =
      some (body, rawLocals code length, .one) := by
    simp only [lookupCodeHOLExact, known, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "compute_jumpdests") (values code length) body (rawLocals code length) .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "code" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals]

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.environment

import InitECandidate.Solver.WitnessRadix.ZeroMemory
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "dst", .one), (ofString "n", .one)]
def values (dst : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word dst), .val (.word (BitVec.ofNat 64 length))]
def rawLocals (dst : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name = ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (dst : BitVec 64) (length : Nat) (code : codeFn (ofString "memzero") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "memzero") (values dst length) = some (body, callee, .one) ∧
      callee.lookup (ofString "dst") = some (.val (.word dst)) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values dst length).length ∧
      ((formals.zip (values dst length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "memzero") (values dst length) =
      some (body, rawLocals dst length, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_, ?_⟩
  · rw [locals]
    have different : ofString "dst" ≠ ofString "n" := by decide
    simp [rawLocals, different]
  · rw [locals]; simp [rawLocals]

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.environment

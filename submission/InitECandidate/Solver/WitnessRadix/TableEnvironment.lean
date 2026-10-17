import InitECandidate.Solver.WitnessRadix.TableState

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "key_len", .one), (ofString "cap", .one)]
def values (capacity : Nat) : List (ValueHOL 64) := [.val (.word 32#64), .val (.word (BitVec.ofNat 64 capacity))]
def rawLocals (capacity : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "cap" then some (.val (.word (BitVec.ofNat 64 capacity)))
  else if name = ofString "key_len" then some (.val (.word 32#64)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (capacity : Nat)
    (code : codeFn (ofString "htab_new") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "htab_new") (values capacity) = some (body, callee, .one) ∧
      callee.lookup (ofString "key_len") = some (.val (.word 32#64)) ∧
      callee.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values capacity).length ∧
      ((formals.zip (values capacity)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "htab_new") (values capacity) =
      some (body, rawLocals capacity, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_, ?_⟩
  · rw [locals]
    have different : ofString "key_len" ≠ ofString "cap" := by decide
    simp [rawLocals, different]
  · rw [locals]; simp [rawLocals]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.environment

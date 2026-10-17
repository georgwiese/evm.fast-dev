import InitECandidate.Solver.WitnessRadix.PersistentAlloc
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "n", .one)]
def values (amount : BitVec 64) : List (ValueHOL 64) := [.val (.word amount)]
def rawLocals (amount : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word amount)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (amount : BitVec 64) (code : codeFn (ofString "alloc") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "alloc") (values amount) = some (body, callee, .one) ∧
      callee.lookup (ofString "n") = some (.val (.word amount)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values amount).length ∧
      ((formals.zip (values amount)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "alloc") (values amount) =
      some (body, rawLocals amount, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_⟩
  rw [locals]
  simp [rawLocals]

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.environment

import InitECandidate.Solver.MutableTable.GrowProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.MutableTable.Grow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "t", .one)]
def values (table : BitVec 64) : List (ValueHOL 64) := [.val (.word table)]
def rawLocals (table : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "t" then some (.val (.word table)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (table : BitVec 64) (code : codeFn (ofString "htab_grow") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "htab_grow") (values table) = some (body, callee, .one) ∧
      callee.lookup (ofString "t") = some (.val (.word table)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values table).length ∧
      ((formals.zip (values table)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_grow") (values table) = some (body, rawLocals table, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, called, ?_⟩
  rw [locals]
  simp [rawLocals]

end InitECandidate.Solver.MutableTable.Grow

#print axioms InitECandidate.Solver.MutableTable.Grow.environment

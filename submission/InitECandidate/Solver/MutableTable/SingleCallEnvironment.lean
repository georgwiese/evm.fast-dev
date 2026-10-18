import InitECandidate.Solver.MutableTable.ReadCallEnvironment

namespace InitECandidate.Solver.MutableTable.ReadCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def singleFormals : List (MlS × ShapeHOL) := [(ofString "t", .one)]
def singleValues (table : BitVec 64) : List (ValueHOL 64) := [.val (.word table)]
def singleLocals (table : BitVec 64) (name : MlS) : Option (ValueHOL 64) := if name = ofString "t" then some (.val (.word table)) else none

theorem single_environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (table : BitVec 64)
    (code : codeFn function = some (singleFormals, body, shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn function (singleValues table) = some (body, callee, shape) ∧
      callee.lookup (ofString "t") = some (.val (.word table)) := by
  have valid : (singleFormals.map Prod.fst).Nodup ∧ singleFormals.length = (singleValues table).length ∧
      ((singleFormals.zip (singleValues table)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [singleFormals, singleValues, shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn function (singleValues table) = some (body, singleLocals table, shape) := by
    simp only [lookupCodeHOLExact, code, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, called, ?_⟩
  rw [locals]
  simp [singleLocals]

end InitECandidate.Solver.MutableTable.ReadCall

#print axioms InitECandidate.Solver.MutableTable.ReadCall.single_environment

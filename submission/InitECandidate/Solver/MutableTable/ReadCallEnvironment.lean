import InitECandidate.Solver.MutableTable.PureValueCall
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.MutableTable.ReadCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals (second : String) : List (MlS × ShapeHOL) := [(ofString "t", .one), (ofString second, .one)]
def values (table argument : BitVec 64) : List (ValueHOL 64) := [.val (.word table), .val (.word argument)]
def rawLocals (second : String) (table argument : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString second then some (.val (.word argument)) else if name = ofString "t" then some (.val (.word table)) else none

/-- The original two-scalar table-reader ABI, allowing each actual parameter
name and scalar/tuple return shape without changing its source program. -/
theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (second : String) (distinct : ofString "t" ≠ ofString second)
    (table argument : BitVec 64) (code : codeFn function = some (formals second, body, shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn function (values table argument) = some (body, callee, shape) ∧
      callee.lookup (ofString "t") = some (.val (.word table)) ∧ callee.lookup (ofString second) = some (.val (.word argument)) := by
  have valid : ((formals second).map Prod.fst).Nodup ∧ (formals second).length = (values table argument).length ∧
      (((formals second).zip (values table argument)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, distinct, shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn function (values table argument) = some (body, rawLocals second table argument, shape) := by
    simp only [lookupCodeHOLExact, code, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, called, ?_, ?_⟩
  all_goals rw [locals]
  · simp [rawLocals, distinct]
  · simp [rawLocals]

end InitECandidate.Solver.MutableTable.ReadCall

#print axioms InitECandidate.Solver.MutableTable.ReadCall.environment

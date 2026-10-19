import InitECandidate.Solver.Mpt.StorageSetProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input.RlpWrite

def values (address key : BitVec 64) (words : U256Value.Words) : List (ValueHOL 64) :=
  [.val (.word address),.val (.word key),U256Value.tuple words]
def rawLocals (address key : BitVec 64) (words : U256Value.Words) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "value" then some (U256Value.tuple words)
  else if name = ofString "key" then some (.val (.word key))
  else if name = ofString "addr" then some (.val (.word address)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (address key : BitVec 64) (words : U256Value.Words)
    (lookup : codeFn (ofString "set_storage") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "set_storage") (values address key words) = some (body,callee,.one) ∧
      callee.lookup (ofString "addr") = some (.val (.word address)) ∧ callee.lookup (ofString "key") = some (.val (.word key)) ∧
      callee.lookup (ofString "value") = some (U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values address key words).length ∧
      ((formals.zip (values address key words)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,TransientSet.formals,values,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "addr" ≠ ofString "key" by decide,show ofString "addr" ≠ ofString "value" by decide,
      show ofString "key" ≠ ofString "value" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "set_storage") (values address key words) = some (body,rawLocals address key words,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "addr" ≠ ofString "value" by decide,show ofString "addr" ≠ ofString "key" by decide]
  · simp [rawLocals,show ofString "key" ≠ ofString "value" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.environment

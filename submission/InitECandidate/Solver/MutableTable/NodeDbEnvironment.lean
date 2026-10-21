import InitECandidate.Solver.MutableTable.NodeDbOriginalCode

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def resultShape : ShapeHOL := .comb [.one,.one,.one]
def arguments (table query : BitVec 64) : List (ValueHOL 64) := [.val (.word table),.val (.word query)]
def rawLocals (table query : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "hash" then some (.val (.word query)) else if name=ofString "db" then some (.val (.word table)) else none

/-- Actual two-word argument lookup and original triple result shape. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (table query : BitVec 64)
    (known : codeFn (ofString "nodedb_lookup")=some (formals,body,resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "nodedb_lookup") (arguments table query)=some (body,callee,resultShape) ∧
      callee.lookup (ofString "db")=some (.val (.word table)) ∧ callee.lookup (ofString "hash")=some (.val (.word query)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(arguments table query).length ∧
      ((formals.zip (arguments table query)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,arguments,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "nodedb_lookup") (arguments table query)=some (body,rawLocals table query,resultShape) := by
    simp only [lookupCodeHOLExact,known,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "db"≠ofString "hash" from by decide],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.environment

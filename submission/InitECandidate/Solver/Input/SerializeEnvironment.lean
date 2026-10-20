import InitECandidate.Solver.Input.SerializeProgram

namespace InitECandidate.Solver.Input.Serialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (out root succ chain schema : BitVec 64) : List (ValueHOL 64) := [.val (.word out),.val (.word root),.val (.word succ),.val (.word chain),.val (.word schema)]
def rawLocals (out root succ chain schema : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "schema_id" then some (.val (.word schema)) else if name = ofString "chain_id" then some (.val (.word chain)) else
  if name = ofString "succ" then some (.val (.word succ)) else if name = ofString "root" then some (.val (.word root)) else if name = ofString "out" then some (.val (.word out)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (out root succ chain schema : BitVec 64)
    (known : codeFn (ofString "serialize_result") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "serialize_result") (values out root succ chain schema) = some (body,callee,.one) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) ∧ callee.lookup (ofString "root") = some (.val (.word root)) ∧
      callee.lookup (ofString "succ") = some (.val (.word succ)) ∧ callee.lookup (ofString "chain_id") = some (.val (.word chain)) ∧ callee.lookup (ofString "schema_id") = some (.val (.word schema)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values out root succ chain schema).length ∧
      ((formals.zip (values out root succ chain schema)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "serialize_result") (values out root succ chain schema) = some (body,rawLocals out root succ chain schema,.one) := by
    simp only [lookupCodeHOLExact,known,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ body _ .one raw
  refine ⟨callee,called,?_,?_,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,show ofString "out" ≠ ofString "root" from by decide,show ofString "out" ≠ ofString "succ" from by decide,show ofString "out" ≠ ofString "chain_id" from by decide,show ofString "out" ≠ ofString "schema_id" from by decide,show ofString "root" ≠ ofString "succ" from by decide,show ofString "root" ≠ ofString "chain_id" from by decide,show ofString "root" ≠ ofString "schema_id" from by decide,show ofString "succ" ≠ ofString "chain_id" from by decide,show ofString "succ" ≠ ofString "schema_id" from by decide,show ofString "chain_id" ≠ ofString "schema_id" from by decide]

end InitECandidate.Solver.Input.Serialize

#print axioms InitECandidate.Solver.Input.Serialize.environment

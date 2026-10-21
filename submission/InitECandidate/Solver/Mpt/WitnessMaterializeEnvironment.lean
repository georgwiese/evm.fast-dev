import InitECandidate.Solver.Mpt.WitnessMaterializeProgram

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (db pointer length : BitVec 64) : List (ValueHOL 64) := [.val (.word db),.val (.word pointer),.val (.word length)]
def rawLocals (db pointer length : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word length)) else if name=ofString "p" then some (.val (.word pointer)) else
    if name=ofString "db" then some (.val (.word db)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (db pointer length : BitVec 64)
    (known : codeFn (ofString "_decode_witness_node")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_decode_witness_node") (values db pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "n")=some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values db pointer length).length ∧
      ((formals.zip (values db pointer length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "_decode_witness_node") (values db pointer length)=some (body,rawLocals db pointer length,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,show ofString "db"≠ofString "n" from by decide,
    show ofString "db"≠ofString "p" from by decide,show ofString "p"≠ofString "n" from by decide]

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.environment

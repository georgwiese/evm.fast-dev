import InitECandidate.Solver.Mpt.WitnessCoreProgram
import InitECandidate.Solver.Mpt.WitnessMaterializeEnvironment

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (db pointer length mark : BitVec 64) : List (ValueHOL 64) := [.val (.word db),.val (.word pointer),.val (.word length),.val (.word mark)]
def rawLocals (db pointer length mark : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "mark" then some (.val (.word mark)) else if name=ofString "n" then some (.val (.word length)) else
    if name=ofString "p" then some (.val (.word pointer)) else if name=ofString "db" then some (.val (.word db)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (db pointer length mark : BitVec 64)
    (known : codeFn (ofString "_decode_witness_node_mpt")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_decode_witness_node_mpt") (values db pointer length mark)=some (body,callee,.one) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word length)) ∧ callee.lookup (ofString "mark")=some (.val (.word mark)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values db pointer length mark).length ∧
      ((formals.zip (values db pointer length mark)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "_decode_witness_node_mpt") (values db pointer length mark)=some (body,rawLocals db pointer length mark,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,show ofString "db"≠ofString "mark" from by decide,
    show ofString "db"≠ofString "n" from by decide,show ofString "db"≠ofString "p" from by decide,
    show ofString "p"≠ofString "mark" from by decide,show ofString "p"≠ofString "n" from by decide,
    show ofString "n"≠ofString "mark" from by decide]

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (db pointer length : BitVec 64)
    (known : codeFn (ofString "_decode_witness_node_body")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_decode_witness_node_body") (WitnessMaterialize.values db pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "n")=some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(WitnessMaterialize.values db pointer length).length ∧
      ((formals.zip (WitnessMaterialize.values db pointer length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,WitnessMaterialize.formals,WitnessMaterialize.values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "_decode_witness_node_body") (WitnessMaterialize.values db pointer length)=
      some (body,WitnessMaterialize.rawLocals db pointer length,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]; simp [WitnessMaterialize.rawLocals,show ofString "db"≠ofString "n" from by decide,
    show ofString "db"≠ofString "p" from by decide,show ofString "p"≠ofString "n" from by decide]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.environment
#print axioms InitECandidate.Solver.Mpt.WitnessCore.environment

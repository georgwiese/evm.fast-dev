import InitECandidate.Solver.Mpt.WitnessDecodeRootProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (db root : BitVec 64) : List (ValueHOL 64) := [.val (.word db),.val (.word root)]
def rawLocals (db root : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "root_hash" then some (.val (.word root)) else if name=ofString "db" then some (.val (.word db)) else none

/-- Original root decoder ABI at the actual node table and root pointer. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (db root : BitVec 64)
    (known : codeFn (ofString "decode_witness_to_mpt")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "decode_witness_to_mpt") (values db root)=some (body,callee,.one) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "root_hash")=some (.val (.word root)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values db root).length ∧
      ((formals.zip (values db root)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "decode_witness_to_mpt") (values db root)=some (body,rawLocals db root,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "db"≠ofString "root_hash" from by decide],
    by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.environment

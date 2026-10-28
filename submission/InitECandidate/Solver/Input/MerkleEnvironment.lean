import InitECandidate.Solver.Input.MerkleProgram

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p n limit out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word n),.val (.word limit),.val (.word out)]
def rawLocals (p n limit out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "limit" then some (.val (.word limit))
  else if name=ofString "n" then some (.val (.word n)) else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p n limit out : BitVec 64)
    (code : codeFn (ofString "merkleize")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "merkleize") (values p n limit out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word n)) ∧
      callee.lookup (ofString "limit")=some (.val (.word limit)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n limit out).length ∧
      ((formals.zip (values p n limit out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "merkleize") (values p n limit out)=some (body,rawLocals p n limit out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "limit" from by decide,
    show ofString "p"≠ofString "n" from by decide,show ofString "n"≠ofString "out" from by decide,
    show ofString "n"≠ofString "limit" from by decide,show ofString "limit"≠ofString "out" from by decide]

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.environment

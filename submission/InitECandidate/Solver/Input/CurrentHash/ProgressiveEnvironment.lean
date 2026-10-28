import InitECandidate.Solver.Input.CurrentHash.ProgressiveProgram

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p n out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word n),.val (.word out)]
def rawLocals (p n out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "n" then some (.val (.word n))
  else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p n out : BitVec 64)
    (code : codeFn (ofString "merkleize_progressive")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "merkleize_progressive") (values p n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word n)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n out).length ∧
      ((formals.zip (values p n out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "merkleize_progressive") (values p n out)=some (body,rawLocals p n out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,show ofString "p"≠ofString "out" from by decide,show ofString "p"≠ofString "n" from by decide,show ofString "n"≠ofString "out" from by decide]

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.environment

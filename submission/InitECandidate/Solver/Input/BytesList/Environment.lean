import InitECandidate.Solver.Input.BytesList.BodyNormal

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def values (pointer length limit maximum : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word length),.val (.word limit),.val (.word maximum)]
def rawLocals (pointer length limit maximum : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "maxb" then some (.val (.word maximum)) else if name=ofString "lim" then some (.val (.word limit))
  else if name=ofString "len" then some (.val (.word length)) else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer length limit maximum : BitVec 64)
    (lookup : codeFn (ofString "decode_bytes_list")=some (formals,body,VarList.returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "decode_bytes_list") (values pointer length limit maximum)=some (body,callee,VarList.returnShape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) ∧
      callee.lookup (ofString "lim")=some (.val (.word limit)) ∧ callee.lookup (ofString "maxb")=some (.val (.word maximum)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length limit maximum).length ∧
      ((formals.zip (values pointer length limit maximum)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "decode_bytes_list") (values pointer length limit maximum)=
      some (body,rawLocals pointer length limit maximum,VarList.returnShape) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "maxb" from by decide,show ofString "p"≠ofString "lim" from by decide,show ofString "p"≠ofString "len" from by decide]
  · simp [rawLocals,show ofString "len"≠ofString "maxb" from by decide,show ofString "len"≠ofString "lim" from by decide]
  · simp [rawLocals,show ofString "lim"≠ofString "maxb" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.environment

import InitECandidate.Solver.Input.FixedList.Normal

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def values (length size limit : BitVec 64) : List (ValueHOL 64) := [.val (.word length),.val (.word size),.val (.word limit)]
def rawLocals (length size limit : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "lim" then some (.val (.word limit)) else if name=ofString "sz" then some (.val (.word size))
  else if name=ofString "len" then some (.val (.word length)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (length size limit : BitVec 64)
    (lookup : codeFn (ofString "ssz_fixed_list_count")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "ssz_fixed_list_count") (values length size limit)=some (body,callee,.one) ∧
      callee.lookup (ofString "len")=some (.val (.word length)) ∧ callee.lookup (ofString "sz")=some (.val (.word size)) ∧
      callee.lookup (ofString "lim")=some (.val (.word limit)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values length size limit).length ∧
      ((formals.zip (values length size limit)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "ssz_fixed_list_count") (values length size limit)=some (body,rawLocals length size limit,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "len"≠ofString "lim" from by decide,show ofString "len"≠ofString "sz" from by decide]
  · simp [rawLocals,show ofString "sz"≠ofString "lim" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.environment

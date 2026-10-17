import InitECandidate.Solver.MutableTable.HasProgram

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (table key : BitVec 64)
    (code : codeFn (ofString "htab_has")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htab_has") [.val (.word table),.val (.word key)]=some (body,callee,.one) ∧
      callee.lookup (ofString "t")=some (.val (.word table)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word table),.val (.word key)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word table),.val (.word key)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,Find.formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_has") [.val (.word table),.val (.word key)]=some (body,Find.rawLocals table key,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [Find.rawLocals,show ofString "t"≠ofString "key" from by decide]
  · simp [Find.rawLocals]

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.environment

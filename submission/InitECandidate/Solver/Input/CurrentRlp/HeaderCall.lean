import InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (header : BitVec 64)
    (lookup : codeFn (ofString "encode_header")=some (HeaderEncoding.formals,body,HeaderEncoding.returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "encode_header") [.val (.word header)]=some (body,callee,HeaderEncoding.returnShape) ∧
      callee.lookup (ofString "h")=some (.val (.word header)) := by
  have valid : (HeaderEncoding.formals.map Prod.fst).Nodup ∧ HeaderEncoding.formals.length=([.val (.word header)] : List (ValueHOL 64)).length ∧
      ((HeaderEncoding.formals.zip [.val (.word header)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [HeaderEncoding.formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "encode_header") [.val (.word header)]=
      some (body,CallNormal.unaryLocals "h" header,HeaderEncoding.returnShape) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [CallNormal.unaryLocals]

end InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.environment

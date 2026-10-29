import InitECandidate.Solver.Input.CurrentRlp.BlockLength

namespace InitECandidate.Solver.Input.CurrentRlp.BlockLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix RlpLength

def rawLocals (header payload : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "pl" then some (.val (.word payload)) else if name=ofString "hdr" then some (.val (.word header)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (header payload : BitVec 64)
    (lookup : codeFn (ofString "block_rlp_length")=some (Block.formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "block_rlp_length") [.val (.word header),.val (.word payload)]=some (body,callee,.one) ∧
      callee.lookup (ofString "hdr")=some (.val (.word header)) ∧ callee.lookup (ofString "pl")=some (.val (.word payload)) := by
  have valid : (Block.formals.map Prod.fst).Nodup ∧ Block.formals.length=([.val (.word header),.val (.word payload)] : List (ValueHOL 64)).length ∧
      ((Block.formals.zip [.val (.word header),.val (.word payload)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [Block.formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "block_rlp_length") [.val (.word header),.val (.word payload)]=some (body,rawLocals header payload,.one):=by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "hdr"≠ofString "pl" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.CurrentRlp.BlockLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.environment

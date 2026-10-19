import InitECandidate.Solver.Mpt.StorageKeyProgram

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def rawLocals (address key : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "key" then some (.val (.word key))
  else if name=ofString "addr" then some (.val (.word address)) else none

/-- The literal original two-word ABI supplies the actual finite callee
bindings, independently of a future body execution or model. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (address key : BitVec 64)
    (code : codeFn (ofString "sk_make")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sk_make") ([.val (.word address),.val (.word key)] : List (ValueHOL 64))=some (body,callee,.one) ∧
      callee.lookup (ofString "addr")=some (.val (.word address)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word address),.val (.word key)] : List (ValueHOL 64)).length ∧
      ((formals.zip ([.val (.word address),.val (.word key)] : List (ValueHOL 64))).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "sk_make") ([.val (.word address),.val (.word key)] : List (ValueHOL 64))=some (body,rawLocals address key,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "addr"≠ofString "key" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.environment

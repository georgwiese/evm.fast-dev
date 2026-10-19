import InitECandidate.Solver.Mpt.AccountCommitProgram

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def rawLocals (address account : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "a" then some (.val (.word account))
  else if name=ofString "addr" then some (.val (.word address)) else none

/-- The literal original two-word ABI supplies the actual finite callee
bindings, independently of a future body execution or model. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (address account : BitVec 64)
    (code : codeFn (ofString "modify_state_commit")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "modify_state_commit") (AccountSet.values address account)=some (body,callee,.one) ∧
      callee.lookup (ofString "addr")=some (.val (.word address)) ∧ callee.lookup (ofString "a")=some (.val (.word account)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(AccountSet.values address account).length ∧
      ((formals.zip (AccountSet.values address account)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,AccountSet.values,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "modify_state_commit") (AccountSet.values address account)=some (body,rawLocals address account,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "addr"≠ofString "a" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.environment

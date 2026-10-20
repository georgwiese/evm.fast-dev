import InitECandidate.Solver.Mpt.AccountBalanceSetProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

def values (address : BitVec 64) (words : U256Value.Words) : List (ValueHOL 64) :=
  [.val (.word address),U256Value.tuple words]
def rawLocals (address : BitVec 64) (words : U256Value.Words) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "amount" then some (U256Value.tuple words)
  else if name = ofString "addr" then some (.val (.word address)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (address : BitVec 64) (words : U256Value.Words)
    (lookup : codeFn (ofString "set_account_balance") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "set_account_balance") (values address words) = some (body,callee,.one) ∧
      callee.lookup (ofString "addr") = some (.val (.word address)) ∧
      callee.lookup (ofString "amount") = some (U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values address words).length ∧
      ((formals.zip (values address words)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "addr" ≠ ofString "amount" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "set_account_balance") (values address words) = some (body,rawLocals address words,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "addr" ≠ ofString "amount" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.environment

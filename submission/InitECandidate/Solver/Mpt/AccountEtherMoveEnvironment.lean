import InitECandidate.Solver.Mpt.AccountEtherMoveProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

def values (sender recipient : BitVec 64) (words : U256Value.Words) : List (ValueHOL 64) :=
  [.val (.word sender),.val (.word recipient),U256Value.tuple words]
def rawLocals (sender recipient : BitVec 64) (words : U256Value.Words) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "amount" then some (U256Value.tuple words)
  else if name = ofString "recipient" then some (.val (.word recipient))
  else if name = ofString "sender" then some (.val (.word sender)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (sender recipient : BitVec 64) (words : U256Value.Words)
    (lookup : codeFn (ofString "move_ether") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "move_ether") (values sender recipient words) = some (body,callee,.one) ∧
      callee.lookup (ofString "sender") = some (.val (.word sender)) ∧
      callee.lookup (ofString "recipient") = some (.val (.word recipient)) ∧
      callee.lookup (ofString "amount") = some (U256Value.tuple words) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values sender recipient words).length ∧
      ((formals.zip (values sender recipient words)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "sender" ≠ ofString "recipient" by decide,show ofString "sender" ≠ ofString "amount" by decide,
      show ofString "recipient" ≠ ofString "amount" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "move_ether") (values sender recipient words) = some (body,rawLocals sender recipient words,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "sender" ≠ ofString "amount" by decide,show ofString "sender" ≠ ofString "recipient" by decide]
  · simp [rawLocals,show ofString "recipient" ≠ ofString "amount" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.environment

import InitECandidate.Solver.Mpt.AccountNewProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.AccountNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.RlpWrite

def values (nonce : BitVec 64) (balance : U256Value.Words) (hash : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word nonce),U256Value.tuple balance,.val (.word hash)]
def rawLocals (nonce : BitVec 64) (balance : U256Value.Words) (hash : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "code_hash" then some (.val (.word hash))
  else if name=ofString "balance" then some (U256Value.tuple balance)
  else if name=ofString "nonce" then some (.val (.word nonce)) else none

theorem environment (codeFn : MlS → Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (nonce : BitVec 64) (balance : U256Value.Words) (hash : BitVec 64)
    (lookup : codeFn (ofString "acct_new")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "acct_new") (values nonce balance hash)=some (body,callee,.one) ∧
      callee.lookup (ofString "nonce")=some (.val (.word nonce)) ∧
      callee.lookup (ofString "balance")=some (U256Value.tuple balance) ∧
      callee.lookup (ofString "code_hash")=some (.val (.word hash)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values nonce balance hash).length ∧
      ((formals.zip (values nonce balance hash)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,U256Value.tupleShape,U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "nonce"≠ofString "balance" by decide,show ofString "nonce"≠ofString "code_hash" by decide,
      show ofString "balance"≠ofString "code_hash" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "acct_new") (values nonce balance hash)=some (body,rawLocals nonce balance hash,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "nonce"≠ofString "code_hash" by decide,show ofString "nonce"≠ofString "balance" by decide]
  · simp [rawLocals,show ofString "balance"≠ofString "code_hash" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.AccountNew

#print axioms InitECandidate.Solver.Mpt.AccountNew.environment

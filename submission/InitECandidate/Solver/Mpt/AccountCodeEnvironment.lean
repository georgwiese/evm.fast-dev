import InitECandidate.Solver.Mpt.AccountCodeProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input.RlpWrite

def values (address codePointer : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word address),.val (.word codePointer),.val (.word (BitVec.ofNat 64 length))]
def rawLocals (address codePointer : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "code_len" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name = ofString "code" then some (.val (.word codePointer))
  else if name = ofString "addr" then some (.val (.word address)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (address codePointer : BitVec 64) (length : Nat)
    (lookup : codeFn (ofString "set_code") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "set_code") (values address codePointer length) = some (body,callee,.one) ∧
      callee.lookup (ofString "addr") = some (.val (.word address)) ∧ callee.lookup (ofString "code") = some (.val (.word codePointer)) ∧
      callee.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values address codePointer length).length ∧
      ((formals.zip (values address codePointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,formals,values,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "addr" ≠ ofString "code" by decide,show ofString "addr" ≠ ofString "code_len" by decide,
      show ofString "code" ≠ ofString "code_len" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "set_code") (values address codePointer length) = some (body,rawLocals address codePointer length,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "addr" ≠ ofString "code_len" by decide,show ofString "addr" ≠ ofString "code" by decide]
  · simp [rawLocals,show ofString "code" ≠ ofString "code_len" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.environment

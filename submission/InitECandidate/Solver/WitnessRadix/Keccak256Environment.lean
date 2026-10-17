import InitECandidate.Solver.WitnessRadix.Keccak256Program

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)]
def values (pointer out : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 length)),.val (.word out)]
def rawLocals (pointer out : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer out : BitVec 64) (length : Nat)
    (code : codeFn (ofString "keccak256")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak256") (values pointer out length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer out length).length ∧
      ((formals.zip (values pointer out length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "keccak256") (values pointer out length)=some (body,rawLocals pointer out length,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,lookup,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,lookup,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.environment

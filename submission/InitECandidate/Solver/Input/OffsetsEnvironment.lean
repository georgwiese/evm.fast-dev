import InitECandidate.Solver.Input.OffsetsNormal

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS×ShapeHOL) :=
  [(ofString "offs",.one),(ofString "n",.one),(ofString "fixed",.one),(ofString "len",.one)]
def arguments (pointer fixed total : BitVec 64) (count : Nat) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 count)),.val (.word fixed),.val (.word total)]
def rawLocals (pointer fixed total : BitVec 64) (count : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "len" then some (.val (.word total))
  else if name=ofString "fixed" then some (.val (.word fixed))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 count)))
  else if name=ofString "offs" then some (.val (.word pointer)) else none

/-- The actual fixed code entry establishes all four callee bindings. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (pointer fixed total : BitVec 64) (count : Nat)
    (code : codeFn (ofString "ssz_check_offsets")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "ssz_check_offsets") (arguments pointer fixed total count)=some (body,callee,.one) ∧
      callee.lookup (ofString "offs")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      callee.lookup (ofString "fixed")=some (.val (.word fixed)) ∧
      callee.lookup (ofString "len")=some (.val (.word total)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(arguments pointer fixed total count).length ∧
      ((formals.zip (arguments pointer fixed total count)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,arguments,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "ssz_check_offsets") (arguments pointer fixed total count)=
      some (body,rawLocals pointer fixed total count,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "offs"≠ofString "len" from by decide,
      show ofString "offs"≠ofString "fixed" from by decide,show ofString "offs"≠ofString "n" from by decide]
  · simp [rawLocals,show ofString "n"≠ofString "len" from by decide,show ofString "n"≠ofString "fixed" from by decide]
  · simp [rawLocals,show ofString "fixed"≠ofString "len" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.environment

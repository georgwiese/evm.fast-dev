import InitECandidate.Solver.WitnessRadix.ConstructorPlan

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "slice_arr",.one),(ofString "n",.one)]
def values (records count : Nat) : List (ValueHOL 64) := [.val (.word (BitVec.ofNat 64 records)),.val (.word (BitVec.ofNat 64 count))]
def rawLocals (records count : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 count)))
  else if name=ofString "slice_arr" then some (.val (.word (BitVec.ofNat 64 records))) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (records count : Nat)
    (code : codeFn (ofString "nodedb_build")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "nodedb_build") (values records count)=some (body,callee,.one) ∧
      callee.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 records))) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values records count).length ∧
      ((formals.zip (values records count)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "nodedb_build") (values records count)=some (body,rawLocals records count,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,lookup,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,lookup,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.environment

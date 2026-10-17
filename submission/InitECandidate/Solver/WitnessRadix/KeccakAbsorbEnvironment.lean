import InitECandidate.Solver.WitnessRadix.KeccakAbsorbProgram

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "stp",.one),(ofString "blk",.one)]
def values (stp blk : BitVec 64) : List (ValueHOL 64) := [.val (.word stp),.val (.word blk)]
def rawLocals (stp blk : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "blk" then some (.val (.word blk))
  else if name = ofString "stp" then some (.val (.word stp)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (stp blk : BitVec 64)
    (code : codeFn (ofString "keccak_absorb_block") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak_absorb_block") (values stp blk) = some (body,callee,.one) ∧
      callee.lookup (ofString "stp") = some (.val (.word stp)) ∧
      callee.lookup (ofString "blk") = some (.val (.word blk)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values stp blk).length ∧
      ((formals.zip (values stp blk)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "keccak_absorb_block") (values stp blk) = some (body,rawLocals stp blk,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,lookup,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,lookup,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.environment

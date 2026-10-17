import InitECandidate.Solver.MutableTable.WitnessBuildProgram
import InitECandidate.Solver.WitnessRadix.ConstructorEnvironment
import Flapjack.FiniteMap.MapKeys

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem environment_body (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (records count : Nat) (program : ProgHOL 64)
    (code : codeFn (ofString "nodedb_build") = some (Constructor.formals, program, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "nodedb_build") (Constructor.values records count) = some (program, callee, .one) ∧
      callee.lookup = Constructor.rawLocals records count := by
  have valid : (Constructor.formals.map Prod.fst).Nodup ∧ Constructor.formals.length = (Constructor.values records count).length ∧
      ((Constructor.formals.zip (Constructor.values records count)).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [Constructor.formals, Constructor.values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "nodedb_build") (Constructor.values records count) =
      some (program, Constructor.rawLocals records count, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  exact CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw

/-- Both concrete constructor code entries use exactly the same finite ABI
environment, even though their function bodies and remaining code differ. -/
theorem paired_environments (source right : PanSemStateFiniteExact 64 Guest.HostMemory) (records count : Nat)
    (leftCode : source.code.lookup (ofString "nodedb_build") = some (Constructor.formals, body, .one))
    (rightCode : right.code.lookup (ofString "nodedb_build") = some (Constructor.formals, Constructor.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "nodedb_build") (Constructor.values records count) = some (body, callee, .one) ∧
      lookupCodeHOLFinite right.code.lookup (ofString "nodedb_build") (Constructor.values records count) = some (Constructor.body, callee, .one) ∧
      callee.lookup (ofString "slice_arr") = some (.val (.word (BitVec.ofNat 64 records))) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) := by
  obtain ⟨leftCallee, leftLookup, leftLocals⟩ := environment_body source.code.lookup records count body leftCode
  obtain ⟨rightCallee, rightLookup, rightLocals⟩ := environment_body right.code.lookup records count Constructor.body rightCode
  have calleeEq : leftCallee = rightCallee := by
    apply HolFiniteMapExact.ext_lookup
    intro name
    rw [leftLocals, rightLocals]
  rw [← calleeEq] at rightLookup
  refine ⟨leftCallee, leftLookup, rightLookup, ?_, ?_⟩
  all_goals rw [leftLocals]; simp [Constructor.rawLocals, ofString]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.environment_body
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_environments

import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.WitnessRadix.BuildProgram

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "t", .one), (ofString "n", .one)]
def values (table count : BitVec 64) : List (ValueHOL 64) := [.val (.word table), .val (.word count)]
def rawLocals (table count : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word count))
  else if name = ofString "t" then some (.val (.word table)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (table count : BitVec 64)
    (code : codeFn (ofString "solver_radix_index") = some (formals, BuildProgram.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "solver_radix_index") (values table count) = some (BuildProgram.body, callee, .one) ∧
      callee.lookup (ofString "t") = some (.val (.word table)) ∧
      callee.lookup (ofString "n") = some (.val (.word count)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values table count).length ∧
      ((formals.zip (values table count)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "solver_radix_index") (values table count) =
      some (BuildProgram.body, rawLocals table count, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_, ?_⟩
  · rw [locals]
    have different : ofString "t" ≠ ofString "n" := by decide
    simp [rawLocals, different]
  · rw [locals]
    simp [rawLocals]

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.environment

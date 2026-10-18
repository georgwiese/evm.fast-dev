import InitECandidate.Solver.GasBudget.ArithmeticEffectsCall
import InitECandidate.Solver.Input.LocalEffectsPrefix

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.LocalEffects

/-- Actual scoped calls to the44 original arithmetic helpers reach their
real continuation with unchanged memory/global state and a genuinely
returned shaped value. No argument-evaluation or callee-run premise. -/
theorem scoped_prefix (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment source.code) (name : String) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape kind.name arguments continuation) = (some (.returned value), post)) :
    ∃ clock returned inner, clock < source.clock ∧ shapeEqHOL (shapeOfHOLExact returned) shape = true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := clock}) continuation = (some (.returned value), inner) ∧
      post = WitnessRadix.QueryBranch.restore source name inner := by
  apply pure_scoped_prefix source post name shape kind.name arguments continuation _ value normal
  intro values actual callee returnShape lookedUp
  rw [lookup_body source.code kind.name kind.signature.1 kind.body kind.signature.2.2 (environment kind) values actual callee returnShape lookedUp]
  exact original_preserves kind source.code environment

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.scoped_prefix

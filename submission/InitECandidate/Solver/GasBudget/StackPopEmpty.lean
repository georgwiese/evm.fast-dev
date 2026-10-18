import InitECandidate.Solver.GasBudget.StackPopNormal

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real empty-stack path raises EvmErr2 before any stack mutation or
gas charge, at every source clock. It is an opcode exception, not a positive
charge event, and must be followed through the actual frame handler. -/
theorem empty_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word 0#64)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one) :
    ∃ post, evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 2#64))), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite source ∧ post.clock = source.clock := by
  classical
  have spRead := frame_read source frame 16#64 0#64 ev mapped spCell
  let entered := bind source "sp" 0#64
  have spE : entered.locals.lookup (ofString "sp") = some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have testRead : eval entered test = some (.val (.word 1#64)) := by
    simp [eval, test, evalHOLExact, toExact, localVar, spE, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have raised : evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 2#64)) =
      (some (.exception (ofString "EvmErr") (.val (.word 2#64))), emptyLocalsHOLFinite entered) := by
    have shape : entered.eshapes.lookup (ofString "EvmErr") = some .one := exceptionShape
    simp [evaluateHOLFiniteState_raise, shape, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have guardRun : evaluateHOLFiniteState entered guard =
      (some (.exception (ofString "EvmErr") (.val (.word 2#64))), emptyLocalsHOLFinite entered) := by
    simp only [eval] at testRead
    rw [guard, evaluateHOLFiniteState_ite, testRead]
    exact raised
  have tailRun : evaluateHOLFiniteState entered tail =
      (some (.exception (ofString "EvmErr") (.val (.word 2#64))), emptyLocalsHOLFinite entered) := by
    rw [tail, WitnessRadix.StateSteps.stopped_sequence entered (emptyLocalsHOLFinite entered) guard afterGuard _ guardRun (Nat.le_refl _)]
  refine ⟨restore source "sp" (emptyLocalsHOLFinite entered), ?_, rfl, rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "sp" (frameLoad 16#64) 0#64 tail _ spRead tailRun

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.empty_execute

import InitECandidate.Solver.GasBudget.FrameExceptionPrefixView
import InitECandidate.Solver.GasBudget.FrameExceptionHandlerMemory

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem handler_after_frame_prefix (source exceptionPost saved post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : View source) (err : BitVec 64) (paid : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : FramePrefixEffect source exceptionPost view.frame paid)
    (aligned : view.frame.toNat % 8 = 0) (fits : view.frame.toNat + 280 < 2^64)
    (reservoirAway : MemoryWriter.BytesAway (view.frame + 240#64) (view.message + 48#64) 20)
    (normal : evaluateHOLFiniteState (bind {exceptionPost with locals := saved.locals} "err" err) RunFrames.opcodeHandler = (none, post)) :
    paid + (2 + choicePrice err) ≤ source.clock ∧ paid + (2 + choicePrice err) ≤ paid + 3 ∧
      post.clock = source.clock - (paid + (2 + choicePrice err)) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := post.clock} ∧
      regularBudget post.memory view.frame = regularBudget source.memory view.frame ∧
      post.memory (view.continuation + 32#64) = .word 1#64 := by
  let handler := bind {exceptionPost with locals := saved.locals} "err" err
  have handlerEffect : FramePrefixEffect source handler view.frame paid := effect.of_emptyLocals rfl
  let current := view.after_frame_prefix handlerEffect aligned fits reservoirAway
  have installedCurrent : Input.OriginalCode.Installed handler.code := by rw [handlerEffect.code_eq]; exact installed
  have errLocal : handler.locals.lookup (ofString "err") = some (.val (.word err)) := bind_lookup_same _ _ _
  obtain ⟨funded, bounded, clock, frameEq, budget, done⟩ := handler_normal handler post current err installedCurrent errLocal normal
  have fields : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {handler with memory := post.memory, clock := post.clock} := by
    rw [clock]
    exact congrArg emptyLocalsHOLFinite frameEq
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := post.memory, clock := post.clock}) handlerEffect.fields
  refine ⟨?_, by omega, ?_, fields.trans lift, budget.trans handlerEffect.budget, done⟩
  · have first := handlerEffect.fits
    rw [handlerEffect.clock] at funded
    omega
  · rw [clock, handlerEffect.clock]
    omega

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_after_frame_prefix

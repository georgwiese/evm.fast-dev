import InitECandidate.Solver.GasBudget.FrameExceptionView
import InitECandidate.Solver.GasBudget.RunFramesCaughtDispatch

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem handler_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, target)) :
    2 + choicePrice err ≤ source.clock ∧ 2 + choicePrice err ≤ 3 ∧ target.clock = source.clock - (2 + choicePrice err) ∧
      target = {source with memory := target.memory, clock := source.clock - (2 + choicePrice err)} ∧
      regularBudget target.memory view.frame = regularBudget source.memory view.frame ∧
      target.memory (view.continuation + 32#64) = .word 1#64 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "err"] = some [.val (.word err)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, errLocal]
  exact call_normal source target view.frame view.message view.continuation err view.empty view.gas view.spill view.reservoir
    [localVar "err"] args (original_code source.code installed) view.ev view.curCont view.emptyGlobal
    (original_refill_code source.code installed) (original_halt_code source.code installed)
    view.refillMapped view.haltMapped view.messageCell view.gasCell view.spillCell view.reservoirMapped view.reservoirCell
    view.reservoirAway view.continuationAway view.cap normal

/-- An actual caught terminal prefix followed by the original handler marks
the real continuation done and retains the capped physical regular ledger.
The handler view/code/argument are rebuilt, and all clocks are derived. -/
theorem handler_after_prefix (source exceptionPost saved post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : View source) (err : BitVec 64) (paid : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : StackPop.PrefixEffect source exceptionPost view.frame paid)
    (normal : evaluateHOLFiniteState (bind {exceptionPost with locals := saved.locals} "err" err) RunFrames.opcodeHandler = (none, post)) :
    paid + (2 + choicePrice err) ≤ source.clock ∧ paid + (2 + choicePrice err) ≤ paid + 3 ∧
      post.clock = source.clock - (paid + (2 + choicePrice err)) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := post.clock} ∧
      regularBudget post.memory view.frame = regularBudget source.memory view.frame ∧
      post.memory (view.continuation + 32#64) = .word 1#64 := by
  let handler := bind {exceptionPost with locals := saved.locals} "err" err
  have handlerEffect : StackPop.PrefixEffect source handler view.frame paid := effect.of_emptyLocals rfl
  let current := view.after_prefix handlerEffect
  have code := congrArg PanSemStateFiniteExact.code handlerEffect.fields
  change handler.code = source.code at code
  have installedCurrent : Input.OriginalCode.Installed handler.code := by rw [code]; exact installed
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

#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_normal
#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_after_prefix

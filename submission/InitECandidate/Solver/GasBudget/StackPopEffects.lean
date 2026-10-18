import InitECandidate.Solver.GasBudget.StackPopEmpty
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Every outcome of the original pop body spends no call/loop clock.
Its straight-line instructions are still real work. -/
theorem body_clock (code) : Input.QuietClock.Preserves code body := by
  rw [body_shape]
  apply Input.QuietClock.declared
  apply Input.QuietClock.sequence
  · apply Input.QuietClock.conditional
    · exact Input.QuietClock.raised code _ _
    · exact Input.QuietClock.skip code
  · unfold afterGuard
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.assign code _ _
    · apply Input.QuietClock.sequence
      · exact Input.QuietClock.store code _ _
      · exact Input.QuietClock.returned code _

private theorem return_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) :
    emptyLocalsHOLFinite (evaluateHOLFiniteState source (.return expression)).2 = emptyLocalsHOLFinite source := by
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

private theorem raise_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (expression : ExpHOL 64) :
    emptyLocalsHOLFinite (evaluateHOLFiniteState source (.raise name expression)).2 = emptyLocalsHOLFinite source := by
  rw [evaluateHOLFiniteState_raise]
  simp only
  repeat first | rfl | split

/-- All actual outcomes, including underflow, invalid tuple reads and invalid
exception metadata, preserve every nonlocal field except the genuine sp write.
No successful return, stack-data mapping or exception-shape premise is needed. -/
theorem body_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp) :
    emptyLocalsHOLFinite (evaluateHOLFiniteState source body).2 =
      emptyLocalsHOLFinite {source with memory := (if sp = 0#64 then source.memory
        else StoreWord.put source.memory (frame + 16#64) (sp - 1#64))} := by
  classical
  have spRead := frame_read source frame 16#64 sp ev mapped cell
  let entered := bind source "sp" sp
  have spE : entered.locals.lookup (ofString "sp") = some (.val (.word sp)) := bind_lookup_same _ _ _
  have full := Input.ScalarScope.declare_execute source (evaluateHOLFiniteState entered tail).2 "sp"
    (frameLoad 16#64) sp tail (evaluateHOLFiniteState entered tail).1 spRead rfl
  rw [body_shape, full]
  change emptyLocalsHOLFinite (evaluateHOLFiniteState entered tail).2 = _
  by_cases empty : sp = 0#64
  · have testRead : eval entered test = some (.val (.word 1#64)) := by
      simp [eval, test, evalHOLExact, toExact, localVar, spE, empty, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at testRead
    have guardEq : evaluateHOLFiniteState entered guard =
        evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 2#64)) := by
      rw [guard, evaluateHOLFiniteState_ite, testRead]
      simp
    have raisedFrame := raise_frame entered (ofString "EvmErr") (.const 2#64)
    have notNormal := Input.raise_ne_none entered (ofString "EvmErr") (.const 2#64)
    rw [tail, evaluateHOLFiniteState_seq_line780, guardEq]
    generalize computed : evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 2#64)) = output at raisedFrame notNormal ⊢
    obtain ⟨result, middle⟩ := output
    cases result with
    | none => exact False.elim (notNormal rfl)
    | some result =>
      simp only [if_pos empty]
      exact raisedFrame.trans (by rfl)
  · have testRead : eval entered test = some (.val (.word 0#64)) := by
      simp [eval, test, evalHOLExact, toExact, localVar, spE, empty, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have guardRun : evaluateHOLFiniteState entered guard = (none, entered) := by
      simp only [eval] at testRead
      rw [guard, evaluateHOLFiniteState_ite, testRead]
      exact evaluateHOLFiniteState_skip entered
    have decrementRead : eval entered decremented = some (.val (.word (sp - 1#64))) := by
      simp [eval, decremented, evalHOLExact, evalListHOLExact, toExact, localVar, spE, valueIsWord, valueWord, wordOpHOL, wordOp]
    have decrementRun := StateSteps.assign_execute entered "sp" decremented sp (sp - 1#64) spE decrementRead
    let next := bind entered "sp" (sp - 1#64)
    have spN : next.locals.lookup (ofString "sp") = some (.val (.word (sp - 1#64))) := bind_lookup_same _ _ _
    have valueRead : eval next (localVar "sp") = some (.val (.word (sp - 1#64))) := by
      simpa only [eval, localVar, evalHOLExact, toExact] using spN
    have writeRun := StoreWord.execute next (frameAddress 16#64) (localVar "sp") (frame + 16#64) (sp - 1#64)
      (address_read next frame 16#64 ev) valueRead mapped
    rw [tail, StateSteps.next_sequence entered entered guard afterGuard guardRun (Nat.le_refl _)]
    rw [afterGuard, StateSteps.next_sequence entered next decrement _ decrementRun (Nat.le_refl _)]
    rw [StateSteps.next_sequence next _ writeSP (.return returnedValue) writeRun (Nat.le_refl _)]
    rw [return_frame, if_neg empty]
    rfl

theorem body_gas_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp) :
    let target := (evaluateHOLFiniteState source body).2
    target.clock = source.clock ∧ regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      ∀ address, address ≠ frame + 16#64 → target.memory address = source.memory address := by
  have effects := body_frame source frame sp ev mapped cell
  have memory := congrArg PanSemStateFiniteExact.memory effects
  change (evaluateHOLFiniteState source body).2.memory = (if sp = 0#64 then source.memory
    else StoreWord.put source.memory (frame + 16#64) (sp - 1#64)) at memory
  refine ⟨body_clock source.code source rfl, ?_, ?_, ?_⟩
  · rw [memory]
    split
    · rfl
    · exact FrameField.put_budget source.memory frame 16#64 (sp - 1#64) (by decide) (by decide) (by decide)
  · rw [memory]
    split
    · rfl
    · exact FrameField.put_other source.memory frame 16#64 (sp - 1#64) 184#64 (by decide)
  · intro address away
    rw [memory]
    split
    · rfl
    · exact if_neg away

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.body_clock
#print axioms InitECandidate.Solver.GasBudget.StackPop.body_frame
#print axioms InitECandidate.Solver.GasBudget.StackPop.body_gas_frame

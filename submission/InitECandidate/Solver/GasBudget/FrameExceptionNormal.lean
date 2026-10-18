import InitECandidate.Solver.GasBudget.FrameExceptionBranches

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The whole original frame_exception body on its actual normal return.
Rollback refill and the selected halt/direct-error branch preserve the capped
regular ledger. The final real continuation store marks the frame done.
Frame/message ownership and continuation separation remain explicit. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message continuation err empty gas spill reservoir : BitVec 64)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (refillCode : source.code.lookup (ofString "refill_frame_state_gas") = some ([], Refill.body, .one))
    (haltCode : source.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one))
    (refillMapped : ∀ offset ∈ ([64, 72, 112, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (haltMapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame + 112#64) = .word message)
    (gasCell : source.memory (frame + 64#64) = .word gas) (spillCell : source.memory (frame + 192#64) = .word spill)
    (reservoirMapped : source.memaddrs (message + 48#64)) (reservoirCell : source.memory (message + 48#64) = .word reservoir)
    (reservoirAway : message + 48#64 ≠ frame + 64#64)
    (continuationAway : ∀ offset ∈ ([64, 184, 192] : List Nat), frame + BitVec.ofNat 64 offset ≠ continuation + 32#64)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    1 + choicePrice err ≤ source.clock ∧ 1 + choicePrice err ≤ 2 ∧ value = .val (.word 0#64) ∧
      post.clock = source.clock - (1 + choicePrice err) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (1 + choicePrice err)} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧ post.memory (continuation + 32#64) = .word 1#64 := by
  rw [body_shape] at normal
  have refillSafe : Input.LocalPrefix (ofString "err") refill := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨refilled, refillRun, branchRun, _⟩ := refillSafe.normal_continue source post _ value normal
  obtain ⟨refillFits, refillClock, refillFrame, refillBudget⟩ := refill_normal source refilled frame message gas spill reservoir refillCode ev refillMapped messageCell gasCell spillCell
    reservoirMapped reservoirCell reservoirAway cap refillRun
  have refilledEV : refilled.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [refillFrame]; exact ev
  have refilledEmpty : refilled.globals.lookup (ofString "evm_empty") = some (.val (.word empty)) := by rw [refillFrame]; exact emptyGlobal
  have refilledErr : refilled.locals.lookup (ofString "err") = some (.val (.word err)) := by rw [refillFrame]; exact errLocal
  have refilledHalt : refilled.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one) := by rw [refillFrame]; exact haltCode
  have refilledMapped : ∀ offset ∈ ([64, 160, 184] : List Nat), refilled.memaddrs (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    rw [refillFrame]
    exact haltMapped offset member
  have refilledCap : regularBudget refilled.memory frame ≤ 16777216 := by rw [refillBudget]; exact cap
  obtain ⟨chosen, chooseRun, tailRun, _⟩ := choice_safe.normal_continue refilled post (.seq markDone returnZero) value branchRun
  obtain ⟨choiceFits, choiceFrame, choiceBudget⟩ := choice_normal refilled chosen frame err empty refilledErr refilledEV refilledEmpty refilledHalt refilledMapped refilledCap chooseRun
  have baseFrame : chosen = {source with memory := chosen.memory, clock := refilled.clock - choicePrice err} :=
    choiceFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := chosen.memory, clock := refilled.clock - choicePrice err}) refillFrame)
  rw [refillClock] at baseFrame
  have chosenContinuation : chosen.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by rw [baseFrame]; exact continuationGlobal
  have doneSafe : Input.LocalPrefix (ofString "err") markDone := .store _ _
  obtain ⟨done, doneRun, returnRun, _⟩ := doneSafe.normal_continue chosen post returnZero value tailRun
  have addressRead : eval chosen doneAddress = some (.val (.word (continuation + 32#64))) := by
    simp [eval, doneAddress, addConst, evalHOLExact, evalListHOLExact, toExact, chosenContinuation, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨_, doneEq⟩ := Input.word_store_normal chosen done doneAddress (.const 1#64) (continuation + 32#64) 1#64 addressRead rfl doneRun
  have doneFrame : done = {chosen with memory := done.memory} := Input.store_none_frame chosen done doneAddress (.const 1#64) doneRun
  have fullFrame := doneFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := done.memory}) baseFrame)
  have actualReturn : evaluateHOLFiniteState done returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite done) := by
    simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have valueEq := congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have returned : value = .val (.word 0#64) := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using valueEq
  have postEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change post = emptyLocalsHOLFinite done at postEq
  have subtract : source.clock - 1 - choicePrice err = source.clock - (1 + choicePrice err) := by omega
  have doneClock := congrArg PanSemStateFiniteExact.clock fullFrame
  change done.clock = source.clock - 1 - choicePrice err at doneClock
  have postClock : post.clock = source.clock - (1 + choicePrice err) := by rw [postEq]; change done.clock = _; omega
  have calleeFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (1 + choicePrice err)} := by
    rw [postEq]
    have normalized := congrArg emptyLocalsHOLFinite fullFrame
    simpa only [emptyLocalsHOLFinite, subtract] using normalized
  have doneBudget : regularBudget done.memory frame = regularBudget chosen.memory frame := by
    rw [doneEq]
    exact FrameField.put_budget_away chosen.memory frame (continuation + 32#64) 1#64 continuationAway
  refine ⟨by omega, ?_, returned, postClock, calleeFrame, ?_, ?_⟩
  · by_cases same : err = 1#64 <;> simp [choicePrice, same]
  · rw [postEq]
    exact doneBudget.trans (choiceBudget.trans refillBudget)
  · rw [postEq, doneEq]
    change StoreWord.put chosen.memory (continuation + 32#64) 1#64 (continuation + 32#64) = .word 1#64
    simp [StoreWord.put]

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.body_normal

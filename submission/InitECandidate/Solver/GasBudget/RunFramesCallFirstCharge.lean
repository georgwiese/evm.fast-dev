import InitECandidate.Solver.GasBudget.DispatchCallFirstCharge
import InitECandidate.Solver.GasBudget.RunFramesFrameTerminal

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout MemoryWriter Input.RlpWrite

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem caught_call_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (base current capacity pointer scratch sp used : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (aligned : view.frame.toNat % 8 = 0) (queryMapped : BytesMapped source (view.frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : view.frame.toNat + 280 ≤ floor)
    (tableMapped : source.memaddrs (view.frame + 168#64)) (tableCell : source.memory (view.frame + 168#64) = .word (cell plan .header 0))
    (reservoirAway : BytesAway (view.frame + 240#64) (view.message + 48#64) 20)
    (read : eval source opcodeArgument = some (.val (.word 241#64)))
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    FrameTerminal source post view.frame view.continuation (8 * slots.length + 70) ∨
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ 8 * slots.length + 67 ∧
      FrameChargeEvent source ready view.frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      Input.ExecutionTail ready CallOpcode.afterFee none post ∧
      CallOpcode.ChargedLocals ready view.frame view.message current value inStart inSize outStart outSize warm := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post memoryView.installed shapes normal
  have opEq : actualOp = 241#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := (StackPop.PrefixEffect.call_entry source callee view.frame positive).frame_effect
  have entryView : MemoryExtend.View entry view.frame base current capacity pointer scratch := memoryView.after_erase rfl
  have entryTable : TableState entry .account plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, value, inStart, inSize, outStart, outSize, warm, paid, ready, bound, event, surplus, tail, locals⟩ :=
      OpcodeDispatch.call_normal_first_charge entry target view.frame base current capacity pointer scratch view.message entryView aligned queryMapped
        plan slots cursor floor entryTable entryEnvironment separate (view.refillMapped 112 (by decide)) view.messageCell
        tableMapped tableCell view.cap binding _ bodyRun
    rw [zero] at tail
    have callerTail := Input.ExecutionTail.ignored_return tail source .one (by simp [shapeOfHOLExact, shapeEqHOL_eq_true])
    refine Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, 1 + paid, ready, by omega,
      event.prepend before, surplus, ?_, locals⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    rcases OpcodeDispatch.call_exception_first_charge entry target view.frame base current capacity pointer scratch view.message sp view.gas used
        entryView aligned queryMapped plan slots cursor floor entryTable entryEnvironment separate (view.refillMapped 112 (by decide)) view.messageCell
        tableMapped tableCell spMapped spCell (view.refillMapped 64 (by decide)) (view.haltMapped 184 (by decide)) view.gasCell usedCell
        (shapes .EvmErr) view.cap binding (ofString "EvmErr") (.val (.word err)) bodyRun with failed | charged
    · obtain ⟨actualId, actualPayload, paid, bound, effect⟩ := failed
      apply Or.inl
      apply frame_terminal_after_prefix source target post view err (1 + paid) (8 * slots.length + 70) memoryView.installed
        (before.trans effect) aligned memoryView.frameFits reservoirAway handlerRun
      have price : 2 + FrameException.choicePrice err ≤ 3 := by unfold FrameException.choicePrice; split <;> decide
      omega
    · obtain ⟨value, inStart, inSize, outStart, outSize, warm, paid, ready, bound, event, surplus, tail, locals⟩ := charged
      exact Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, 1 + paid, ready, by omega,
        event.prepend before, surplus, .handler tail source (ofString "err") opcodeHandler handlerRun, locals⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_call_first_charge

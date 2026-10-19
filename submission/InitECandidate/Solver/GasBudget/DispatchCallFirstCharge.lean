import InitECandidate.Solver.GasBudget.CallOpcodeFirstCharge
import InitECandidate.Solver.GasBudget.CallOpcodeFirstChargeException
import InitECandidate.Solver.GasBudget.FrameChargePrefix
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.Input.ExecutionTail
import InitECandidate.Solver.Input.EraseClock

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout Input.RlpWrite MemoryWriter

theorem selection_call : tree.choose 241#64 = .invoke "op_call" [] := by rfl

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem call_normal_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : frame.toNat + 280 ≤ floor)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 241#64)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 8 * slots.length + 66 ∧
      FrameChargeEvent source ready frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      Input.ExecutionTail ready CallOpcode.afterFee (some (.returned returned)) post ∧
      CallOpcode.ChargedLocals ready frame message current value inStart inSize outStart outSize warm := by
  obtain ⟨zero, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 241#64 opLocal returned run
  rw [selection_call] at selected
  cases selected
  obtain ⟨positive, values, actualBody, callee, shape, target, actualReturn, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle (ofString "op_call") [] helperRun
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_call") [] CallOpcode.body .one
    (CallOpcode.original_code source.code view.installed) values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have entryView : MemoryExtend.View entry frame base current capacity pointer scratch := view.after_erase rfl
  have entryTable : TableState entry .account plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
  obtain ⟨value, inStart, inSize, outStart, outSize, warm, paid, ready, inner, bound, event, surplus, suffixRun, scope, clock, locals⟩ :=
    CallOpcode.normal_first_charge entry target frame base current capacity pointer scratch message entryView aligned queryMapped
      plan slots cursor floor entryTable entryEnvironment separate messageMapped messageCell tableMapped tableCell cap actualReturn bodyRun
  have tail : Input.ExecutionTail ready CallOpcode.afterFee (some (.returned actualReturn)) target :=
    .locals (.run _ _ suffixRun) (Input.LocalEffects.same_clock scope clock)
  have before := (StackPop.PrefixEffect.call_entry source callee frame positive).frame_effect
  have callerTail := Input.ExecutionTail.ignored_return tail source shape checked
  have actualCallerTail : Input.ExecutionTail ready CallOpcode.afterFee none middle := by
    apply Input.ExecutionTail.locals callerTail
    rw [middleEq]
  have finished : evaluateHOLFiniteState middle (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have rest := Input.ExecutionTail.next actualCallerTail (.return (.const 0#64)) finished
  refine ⟨zero, value, inStart, inSize, outStart, outSize, warm, 1 + paid, ready, by omega,
    event.prepend before, surplus, ?_, locals⟩
  rw [zero]
  apply Input.ExecutionTail.locals rest
  rw [postEq]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem call_exception_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message sp gas used : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : frame.toNat + 280 ≤ floor)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one) (cap : regularBudget source.memory frame ≤ 16777216)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 241#64)))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ (payload = .val (.word 2#64) ∨ payload = .val (.word 8#64) ∨ payload = .val (.word 4#64)) ∧
      ∃ paid, paid ≤ 8 * slots.length + 66 ∧ FramePrefixEffect source post frame paid) ∨
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 8 * slots.length + 66 ∧
      FrameChargeEvent source ready frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      Input.ExecutionTail ready CallOpcode.afterFee (some (.exception identifier payload)) post ∧
      CallOpcode.ChargedLocals ready frame message current value inStart inSize outStart outSize warm := by
  have helperRun := selected_exception source post 241#64 opLocal "op_call" [] selection_call identifier payload run
  obtain ⟨positive, values, actualBody, callee, calleeShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_call") [] identifier payload helperRun
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_call") [] CallOpcode.body .one
    (CallOpcode.original_code source.code view.installed) values actualBody callee calleeShape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have entryView : MemoryExtend.View entry frame base current capacity pointer scratch := view.after_erase rfl
  have entryTable : TableState entry .account plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
  have before := (StackPop.PrefixEffect.call_entry source callee frame positive).frame_effect
  rcases CallOpcode.exception_first_charge entry target frame base current capacity pointer scratch message sp gas used entryView aligned queryMapped
      plan slots cursor floor entryTable entryEnvironment separate messageMapped messageCell tableMapped tableCell spMapped spCell gasMapped usedMapped
      gasCell usedCell shape cap identifier payload bodyRun with failed | charged
  · obtain ⟨actualId, actualPayload, paid, bound, effect⟩ := failed
    have scopes : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
    exact Or.inl ⟨actualId, actualPayload, 1 + paid, by omega, (before.trans effect).of_emptyLocals scopes⟩
  · obtain ⟨value, inStart, inSize, outStart, outSize, warm, paid, ready, inner, bound, event, surplus, suffixRun, scope, clock, locals⟩ := charged
    have tail : Input.ExecutionTail ready CallOpcode.afterFee (some (.exception identifier payload)) target :=
      .locals (.run _ _ suffixRun) (Input.LocalEffects.same_clock scope clock)
    have callerTail := Input.ExecutionTail.ignored_exception tail
    refine Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, 1 + paid, ready, by omega,
      event.prepend before, surplus, ?_, locals⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_call
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.call_normal_first_charge
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.call_exception_first_charge

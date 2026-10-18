import InitECandidate.Solver.GasBudget.OpcodePushSelection
import InitECandidate.Solver.GasBudget.OpcodePushPrefix
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.DispatchNormal

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem push_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (bytes : Nat)
    (bounded : bytes ≤ 32)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word (OpcodePush.opcode bytes))))
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ ready inner returned,
      ChargeEvent source ready frame 2 (OpcodePush.fee (BitVec.ofNat 64 bytes)) ∧
      evaluateHOLFiniteState ready OpcodePush.suffix = (some (.returned returned), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨zero, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post (OpcodePush.opcode bytes) opLocal value normal
  rw [OpcodePush.selection bytes bounded] at selected
  cases selected
  obtain ⟨positive, values, actualBody, callee, shape, target, returned, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle (ofString "op_push") (OpcodePush.arguments bytes) helperRun
  obtain ⟨identified, returnShape, bytesLocal⟩ := OpcodePush.lookup_bytes source bytes opLocal installed values actualBody callee shape args called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨ready, inner, event, suffixRun, scopeEq⟩ := OpcodePush.body_normal_prefix entry target frame (BitVec.ofNat 64 bytes) bytesLocal
    (OriginalCodeEnvironment.stack_pop source.code installed) (OriginalCodeEnvironment.charge_gas source.code installed) ev cap returned bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  refine ⟨zero, ready, inner, returned, event.prepend before, suffixRun, ?_⟩
  rw [postEq, middleEq]
  exact scopeEq

theorem push_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64) (bytes : Nat)
    (bounded : bytes ≤ 32)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word (OpcodePush.opcode bytes))))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ gas < OpcodePush.amount (BitVec.ofNat 64 bytes) ∧ StackPop.PrefixEffect source post frame 2) ∨
    ∃ ready inner, ChargeEvent source ready frame 2 (OpcodePush.fee (BitVec.ofNat 64 bytes)) ∧
      evaluateHOLFiniteState ready OpcodePush.suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  have helperRun := selected_exception source post (OpcodePush.opcode bytes) opLocal "op_push" (OpcodePush.arguments bytes)
    (OpcodePush.selection bytes bounded) identifier payload run
  obtain ⟨positive, values, actualBody, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_push") (OpcodePush.arguments bytes) identifier payload helperRun
  obtain ⟨identified, returnShape, bytesLocal⟩ := OpcodePush.lookup_bytes source bytes opLocal installed values actualBody callee shape args called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have outerScope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases OpcodePush.body_exception_prefix entry target frame sp gas used (BitVec.ofNat 64 bytes) bytesLocal
      (OriginalCodeEnvironment.stack_pop source.code installed) (OriginalCodeEnvironment.charge_gas source.code installed) ev
      spMapped spCell gasMapped usedMapped gasCell usedCell cap (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload bodyRun with insufficient | charged
  · obtain ⟨actualId, actualPayload, unavailable, effect⟩ := insufficient
    exact Or.inl ⟨actualId, actualPayload, unavailable, (before.trans effect).of_emptyLocals outerScope⟩
  · obtain ⟨ready, inner, event, suffixRun, scopeEq⟩ := charged
    exact Or.inr ⟨ready, inner, event.prepend before, suffixRun, outerScope.trans scopeEq⟩

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.push_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.push_exception_prefix

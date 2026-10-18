import InitECandidate.Solver.GasBudget.MemoryOpcodePrefix
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.DispatchNormal

namespace InitECandidate.Solver.GasBudget.MemoryOpcode
def Kind.opcode : Kind → BitVec 64
  | .mload => 81#64 | .mstore => 82#64 | .mstore8 => 83#64
end InitECandidate.Solver.GasBudget.MemoryOpcode

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem selection_memory (kind : MemoryOpcode.Kind) : tree.choose kind.opcode = .invoke kind.label [] := by cases kind <;> rfl

theorem memory_normal_prefix (kind : MemoryOpcode.Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word kind.opcode)))
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ kind.names.length + 25 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready ChargeWithMemory.suffix (some (.returned value)) post := by
  obtain ⟨zero, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post kind.opcode opLocal value normal
  rw [selection_memory] at selected
  cases selected
  obtain ⟨positive, values, actualBody, callee, shape, target, returned, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle kind.name [] helperRun
  have code := MemoryOpcode.original_code kind source.code installed
  have identified := Input.LocalEffects.lookup_body source.code kind.name [] kind.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := MemoryOpcode.body_normal_prefix kind entry target frame installed ev cap returned bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have callerTail := Input.ExecutionTail.ignored_return tail source shape checked
  have actualCallerTail : Input.ExecutionTail ready ChargeWithMemory.suffix none middle := by
    apply Input.ExecutionTail.locals callerTail
    rw [middleEq]
  have finished : evaluateHOLFiniteState middle (.return (.const 0#64)) = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have rest := Input.ExecutionTail.next actualCallerTail (.return (.const 0#64)) finished
  refine ⟨zero, 1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
  rw [zero]
  apply Input.ExecutionTail.locals rest
  rw [postEq]

theorem memory_exception_prefix (kind : MemoryOpcode.Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word kind.opcode)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ kind.names.length + 25 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ kind.names.length + 25 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready ChargeWithMemory.suffix (some (.exception identifier payload)) post := by
  have helperRun := selected_exception source post kind.opcode opLocal kind.label [] (selection_memory kind) identifier payload run
  obtain ⟨positive, values, actualBody, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post kind.name [] identifier payload helperRun
  have code := MemoryOpcode.original_code kind source.code installed
  have identified := Input.LocalEffects.lookup_body source.code kind.name [] kind.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have outerScope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases MemoryOpcode.body_exception_prefix kind entry target frame sp gas used installed shapes ev spMapped spCell gasMapped usedMapped gasCell usedCell cap identifier payload bodyRun with failed | charged
  · obtain ⟨paid, bound, effect⟩ := failed
    exact Or.inl ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals outerScope⟩
  · obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := charged
    have callerTail := Input.ExecutionTail.ignored_exception tail
    refine Or.inr ⟨1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_memory
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.memory_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.memory_exception_prefix

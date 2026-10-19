import InitECandidate.Solver.GasBudget.DispatchRevert
import InitECandidate.Solver.GasBudget.RevertPrechargeErrors

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem revert_error_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 253#64))) (payload : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") payload), post)) :
    payload = .val (.word 1#64) ∨ payload = .val (.word 2#64) ∨ payload = .val (.word 4#64) := by
  have helperRun := selected_exception source post 253#64 opLocal "op_revert" [] selection_revert (ofString "EvmErr") payload normal
  obtain ⟨positive, values, actual, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_revert") [] (ofString "EvmErr") payload helperRun
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_revert") [] RevertOpcode.body .one
    (RevertOpcode.original_code source.code installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  exact RevertOpcode.error_cases (callEntryStateHOLFinite source callee) target installed payload bodyRun

theorem revert_stack_error_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 253#64)))
    (normal : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 2#64))), post)) :
    ∃ paid, paid ≤ 3 ∧ StackPop.PrefixEffect source post frame paid := by
  have helperRun := selected_exception source post 253#64 opLocal "op_revert" [] selection_revert (ofString "EvmErr") (.val (.word 2#64)) normal
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_revert") [] (ofString "EvmErr") (.val (.word 2#64)) helperRun
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_revert") [] RevertOpcode.body .one
    (RevertOpcode.original_code source.code installed) values actual callee returnShape called
  rw [bodyEq] at bodyRun
  obtain ⟨paid, bound, effect⟩ := RevertOpcode.stack_error_prefix (callEntryStateHOLFinite source callee) target frame sp installed ev mapped cell shape bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  exact ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals (by rw [postEq]; rfl)⟩

theorem revert_gas_error_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216) (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 253#64)))
    (normal : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 4#64))), post)) :
    ∃ paid, paid ≤ 25 ∧ StackPop.PrefixEffect source post frame paid := by
  have helperRun := selected_exception source post 253#64 opLocal "op_revert" [] selection_revert (ofString "EvmErr") (.val (.word 4#64)) normal
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_revert") [] (ofString "EvmErr") (.val (.word 4#64)) helperRun
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_revert") [] RevertOpcode.body .one
    (RevertOpcode.original_code source.code installed) values actual callee returnShape called
  rw [bodyEq] at bodyRun
  obtain ⟨paid, bound, effect⟩ := RevertOpcode.gas_error_prefix (callEntryStateHOLFinite source callee) target frame sp gas used installed ev
    spMapped spCell gasMapped usedMapped gasCell usedCell cap shape bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  exact ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals (by rw [postEq]; rfl)⟩

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.revert_error_cases
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.revert_stack_error_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.revert_gas_error_prefix

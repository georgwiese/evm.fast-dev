import InitECandidate.Solver.GasBudget.McopyBodyPrefix
import InitECandidate.Solver.Input.ExecutionTail
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.DispatchNormal

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem selection_mcopy : tree.choose 94#64 = .invoke "op_mcopy" [] := by rfl

theorem mcopy_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 94#64)))
    (view : MemoryExpansionCost.View source frame current)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ Mcopy.names.length + 50 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready Mcopy.suffix (some (.returned value)) post := by
  obtain ⟨zero, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 94#64 opLocal value normal
  rw [selection_mcopy] at selected
  cases selected
  obtain ⟨positive, values, actualBody, callee, shape, target, returned, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle (ofString "op_mcopy") [] helperRun
  have code := Mcopy.original_code source.code view.installed
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_mcopy") [] Mcopy.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, scopeEq⟩ := Mcopy.body_normal_prefix entry target frame current (view.after_erase rfl) cap returned bodyRun
  have tail : Input.ExecutionTail ready Mcopy.suffix (some (.returned returned)) target := .locals (.run _ _ suffixRun) scopeEq
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have callerTail := Input.ExecutionTail.ignored_return tail source shape checked
  have actualCallerTail : Input.ExecutionTail ready Mcopy.suffix none middle := by
    apply Input.ExecutionTail.locals callerTail
    rw [middleEq]
  have finished : evaluateHOLFiniteState middle (.return (.const 0#64)) = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have rest := Input.ExecutionTail.next actualCallerTail (.return (.const 0#64)) finished
  refine ⟨zero, 1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
  rw [zero]
  apply Input.ExecutionTail.locals rest
  rw [postEq]

theorem mcopy_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current sp gas used : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 94#64)))
    (view : MemoryExpansionCost.View source frame current) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ Mcopy.names.length + 50 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ Mcopy.names.length + 50 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready Mcopy.suffix (some (.exception identifier payload)) post := by
  have helperRun := selected_exception source post 94#64 opLocal "op_mcopy" [] (selection_mcopy) identifier payload run
  obtain ⟨positive, values, actualBody, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_mcopy") [] identifier payload helperRun
  have code := Mcopy.original_code source.code view.installed
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_mcopy") [] Mcopy.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have outerScope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases Mcopy.body_exception_prefix entry target frame current sp gas used (view.after_erase rfl) shapes spMapped spCell gasMapped usedMapped gasCell usedCell cap identifier payload bodyRun with failed | charged
  · obtain ⟨paid, bound, effect⟩ := failed
    exact Or.inl ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals outerScope⟩
  · obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, scopeEq⟩ := charged
    have tail : Input.ExecutionTail ready Mcopy.suffix (some (.exception identifier payload)) target := .locals (.run _ _ suffixRun) scopeEq
    have callerTail := Input.ExecutionTail.ignored_exception tail
    refine Or.inr ⟨1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_mcopy
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.mcopy_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.mcopy_exception_prefix

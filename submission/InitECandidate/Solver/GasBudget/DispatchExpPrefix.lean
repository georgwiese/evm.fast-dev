import InitECandidate.Solver.GasBudget.OpcodeExpPrefix
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.DispatchNormal

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem selection_exp : tree.choose 10#64 = .invoke "op_exp" [] := by rfl

theorem exp_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 10#64)))
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ bytes ready inner returned, bytes ≤ 32 ∧ ChargeEvent source ready frame 7 (OpcodeExp.fee bytes) ∧
      evaluateHOLFiniteState ready OpcodeExp.suffix = (some (.returned returned), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨zero, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 10#64 opLocal value normal
  rw [selection_exp] at selected
  cases selected
  obtain ⟨positive, values, actualBody, callee, shape, target, returned, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle (ofString "op_exp") [] helperRun
  have code := OpcodeExp.original_code source.code installed
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_exp") [] OpcodeExp.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨bytes, ready, inner, small, event, suffixRun, scopeEq⟩ := OpcodeExp.body_normal_prefix entry target frame installed ev cap returned bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  refine ⟨zero, bytes, ready, inner, returned, small, event.prepend before, suffixRun, ?_⟩
  rw [postEq, middleEq]
  exact scopeEq

theorem exp_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 10#64)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 7 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ bytes ready inner, bytes ≤ 32 ∧ ChargeEvent source ready frame 7 (OpcodeExp.fee bytes) ∧
      evaluateHOLFiniteState ready OpcodeExp.suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  have helperRun := selected_exception source post 10#64 opLocal "op_exp" [] selection_exp identifier payload run
  obtain ⟨positive, values, actualBody, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_exp") [] identifier payload helperRun
  have code := OpcodeExp.original_code source.code installed
  have identified := Input.LocalEffects.lookup_body source.code (ofString "op_exp") [] OpcodeExp.body .one code values actualBody callee shape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have outerScope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases OpcodeExp.body_exception_prefix entry target frame sp gas used installed shapes ev spMapped spCell gasMapped usedMapped gasCell usedCell cap identifier payload bodyRun with failed | charged
  · obtain ⟨paid, bound, effect⟩ := failed
    exact Or.inl ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals outerScope⟩
  · obtain ⟨bytes, ready, inner, small, event, suffixRun, scopeEq⟩ := charged
    exact Or.inr ⟨bytes, ready, inner, small, event.prepend before, suffixRun, outerScope.trans scopeEq⟩

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_exp
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exp_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exp_exception_prefix

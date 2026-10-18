import InitECandidate.Solver.GasBudget.ChargeWithMemoryPrefix
import InitECandidate.Solver.GasBudget.ChargeWithMemoryLookup
import InitECandidate.Solver.Input.ExecutionTail
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.IgnoredCallException

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real helper caller retains its genuine inner expansion suffix and
caller restoration as a trace after the first positive charge. -/
theorem call_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base : BitVec 64)
    (start size : ExpHOL 64) (installed : Input.OriginalCode.Installed source.code) (positiveBase : 0 < base.toNat)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") [.const base, start, size]) = (none, post)) :
    ∃ paid amount ready, paid ≤ 24 ∧ base ≤ amount ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready suffix none post := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "charge_with_memory") [.const base, start, size] normal
  have identified := Input.LocalEffects.lookup_body source.code (ofString "charge_with_memory") _ body .one
    (original_code source.code installed) values actual callee shape called
  rw [identified] at bodyRun
  have binding := lookup_base source base start size installed values args actual callee shape called
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, scopeEq⟩ :=
    body_normal_prefix entry target frame base installed binding positiveBase ev cap returned bodyRun
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have tail : Input.ExecutionTail ready suffix (some (.returned returned)) inner := .run _ _ suffixRun
  have actualTail : Input.ExecutionTail ready suffix (some (.returned returned)) target := .locals tail scopeEq
  have callerTail := Input.ExecutionTail.ignored_return actualTail source shape checked
  refine ⟨1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
  apply Input.ExecutionTail.locals callerTail
  rw [postEq]

theorem call_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base gas used : BitVec 64)
    (start size : ExpHOL 64) (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (positiveBase : 0 < base.toNat) (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") [.const base, start, size]) = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 24 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ paid amount ready, paid ≤ 24 ∧ base ≤ amount ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready suffix (some (.exception identifier payload)) post := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "charge_with_memory") [.const base, start, size] identifier payload run
  have identified := Input.LocalEffects.lookup_body source.code (ofString "charge_with_memory") _ body .one
    (original_code source.code installed) values actual callee shape called
  rw [identified] at bodyRun
  have binding := lookup_base source base start size installed values args actual callee shape called
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have scopes : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases body_exception_prefix entry target frame base gas used installed shapes binding positiveBase ev spMapped gasMapped usedMapped gasCell usedCell cap
      identifier payload bodyRun with failed | charged
  · obtain ⟨paid, bound, effect⟩ := failed
    exact Or.inl ⟨1 + paid, by omega, (before.trans effect).of_emptyLocals scopes⟩
  · obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, scopeEq⟩ := charged
    have tail : Input.ExecutionTail ready suffix (some (.exception identifier payload)) inner := .run _ _ suffixRun
    have actualTail : Input.ExecutionTail ready suffix (some (.exception identifier payload)) target := .locals tail scopeEq
    have callerTail := Input.ExecutionTail.ignored_exception actualTail
    refine Or.inr ⟨1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_exception_prefix

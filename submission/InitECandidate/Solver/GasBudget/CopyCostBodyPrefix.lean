import InitECandidate.Solver.GasBudget.CopyCostChargePrefix
import InitECandidate.Solver.GasBudget.StackPopsException

namespace InitECandidate.Solver.GasBudget.CopyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_normal_prefix (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body = (some (.returned value), post)) :
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ kind.names.length + 27 ∧ kind.base ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at normal
  obtain ⟨popped, scopedPost, fits, clock, fields, poppedRun, scopeEq, budget, used, outside, depth⟩ :=
    StackPop.pops_normal kind.names source post frame _ (OriginalCodeEnvironment.stack_pop source.code installed) ev value normal
  have before : StackPop.PrefixEffect source popped frame kind.names.length :=
    ⟨fits, clock, by rw [clock]; exact fields, budget, used, outside⟩
  have original : Input.OriginalCode.Installed popped.code := by rw [before.code_eq]; exact installed
  have current : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
  have currentCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, suffixEq⟩ :=
    program_normal_prefix kind popped scopedPost frame original current currentCap value poppedRun
  exact ⟨kind.names.length + paid, amount, ready, inner, by omega, lower, event.prepend before, suffixRun, scopeEq.trans suffixEq⟩

theorem body_exception_prefix (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source kind.body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ kind.names.length + 27 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ kind.names.length + 27 ∧ kind.base ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  rcases StackPop.pops_exception kind.names source post frame sp _ (OriginalCodeEnvironment.stack_pop source.code installed)
      ev spMapped spCell (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload run with failed | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := failed
    exact Or.inl ⟨sp.toNat + 1, by omega, effect⟩
  · obtain ⟨popped, scopedPost, remaining, before, remainingCell, depth, poppedRun, scopeEq⟩ := continued
    have original : Input.OriginalCode.Installed popped.code := by rw [before.code_eq]; exact installed
    have current : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
    have currentCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
    have currentShapes : Input.OriginalExceptions.Installed popped.eshapes := by rw [before.eshapes_eq]; exact shapes
    have currentSp : popped.memaddrs (frame + 16#64) := by rw [before.memaddrs_eq]; exact spMapped
    have currentGas : popped.memaddrs (frame + 64#64) := by rw [before.memaddrs_eq]; exact gasMapped
    have currentUsed : popped.memaddrs (frame + 184#64) := by rw [before.memaddrs_eq]; exact usedMapped
    have currentGasCell : popped.memory (frame + 64#64) = .word gas :=
      (before.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
    have currentUsedCell : popped.memory (frame + 184#64) = .word used := before.used.trans usedCell
    rcases program_exception_prefix kind popped scopedPost frame gas used original currentShapes current currentSp currentGas currentUsed
        currentGasCell currentUsedCell currentCap identifier payload poppedRun with failed | charged
    · obtain ⟨paid, bound, effect⟩ := failed
      exact Or.inl ⟨kind.names.length + paid, by omega, (before.trans effect).of_emptyLocals scopeEq⟩
    · obtain ⟨paid, amount, ready, inner, bound, lower, event, suffixRun, suffixEq⟩ := charged
      exact Or.inr ⟨kind.names.length + paid, amount, ready, inner, by omega, lower, event.prepend before, suffixRun, scopeEq.trans suffixEq⟩

end InitECandidate.Solver.GasBudget.CopyCost

#print axioms InitECandidate.Solver.GasBudget.CopyCost.body_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.CopyCost.body_exception_prefix

import InitECandidate.Solver.GasBudget.McopyException
import InitECandidate.Solver.GasBudget.ChargeEvent
import InitECandidate.Solver.GasBudget.PrefixEnvironment
import InitECandidate.Solver.Input.OriginalExceptions

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem base_positive : 0 < (3 : Nat) := by decide

theorem program_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (view : MemoryExpansionCost.View source frame current)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source program = (some (.returned value), post)) :
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 49 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      evaluateHOLFiniteState ready suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨paid, amount, checkpoint, scopedPost, bound, lower, before, run, scopeEq⟩ := setup_normal source post frame current view value normal
  have original : Input.OriginalCode.Installed checkpoint.code := by rw [before.code_eq]; exact view.installed
  have current : checkpoint.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact view.ev
  have budget : regularBudget checkpoint.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  obtain ⟨ready, inner, fits, clock, fields, suffixRun, suffixEq, budgetEq, credit, depth, outside⟩ :=
    OpcodeChargePrefix.normal [] checkpoint scopedPost frame amount suffix
      (OriginalCodeEnvironment.stack_pop checkpoint.code original) (OriginalCodeEnvironment.charge_gas checkpoint.code original)
      current budget value run
  have amountPositive : 0 < amount.toNat := (base_positive).trans_le lower
  have event : ChargeEvent checkpoint ready frame 1 amount.toNat :=
    ⟨fits, clock, by rw [clock]; exact fields, budgetEq, credit, amountPositive, outside⟩
  exact ⟨paid + 1, amount, ready, inner, by omega, lower, event.prepend before, suffixRun, scopeEq.trans suffixEq⟩

theorem program_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current gas used : BitVec 64)
    (view : MemoryExpansionCost.View source frame current) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (frame + 16#64))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source program = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 49 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 49 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      evaluateHOLFiniteState ready suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨paid, amount, checkpoint, scopedPost, bound, lower, before, chargeRun, scopeEq⟩ :=
    setup_exception source post frame current view identifier payload run
  have original : Input.OriginalCode.Installed checkpoint.code := by rw [before.code_eq]; exact view.installed
  have current : checkpoint.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact view.ev
  have budget : regularBudget checkpoint.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  have currentShape : checkpoint.eshapes.lookup (ofString "EvmErr") = some .one := by
    rw [before.eshapes_eq]; exact shapes Input.OriginalExceptions.Kind.EvmErr
  have currentSp : checkpoint.memaddrs (frame + 16#64) := by rw [before.memaddrs_eq]; exact spMapped
  have currentGas : checkpoint.memaddrs (frame + 64#64) := by rw [before.memaddrs_eq]; exact gasMapped
  have currentUsed : checkpoint.memaddrs (frame + 184#64) := by rw [before.memaddrs_eq]; exact usedMapped
  have currentGasCell : checkpoint.memory (frame + 64#64) = .word gas :=
    (before.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
  have currentUsedCell : checkpoint.memory (frame + 184#64) = .word used := before.used.trans usedCell
  rcases OpcodeChargePrefix.exception [] amount checkpoint scopedPost frame (wordAt checkpoint.memory (frame + 16#64)) gas used suffix
      (OriginalCodeEnvironment.stack_pop checkpoint.code original) (OriginalCodeEnvironment.charge_gas checkpoint.code original)
      current currentSp (memory_word _ _) currentGas currentUsed currentGasCell currentUsedCell budget currentShape identifier payload chargeRun with underflow | insufficient | charged
  · obtain ⟨actualId, actualPayload, impossible, effect, zero⟩ := underflow
    simp at impossible
  · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
    exact Or.inl ⟨paid + 1, by omega, (before.trans effect).of_emptyLocals scopeEq⟩
  · obtain ⟨ready, inner, remaining, effect, suffixRun, suffixEq⟩ := charged
    have event : ChargeEvent checkpoint ready frame 1 amount.toNat :=
      ⟨effect.fits, effect.clock, effect.fields, effect.budget, effect.used, (base_positive).trans_le lower, effect.outside⟩
    exact Or.inr ⟨paid + 1, amount, ready, inner, by omega, lower, event.prepend before, suffixRun, scopeEq.trans suffixEq⟩

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.program_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.Mcopy.program_exception_prefix

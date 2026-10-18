import InitECandidate.Solver.GasBudget.OpcodeExpSetup
import InitECandidate.Solver.GasBudget.ChargeEvent
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.OpcodeExp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_normal_prefix_depth (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ bytes ready inner, bytes ≤ 32 ∧ ChargeEvent source ready frame 6 (fee bytes) ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      evaluateHOLFiniteState ready suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨bytes, checkpoint, scopedPost, small, before, setupDepth, run, scopeEq⟩ := setup_normal source post frame installed ev value normal
  have original : Input.OriginalCode.Installed checkpoint.code := by rw [before.code_eq]; exact installed
  have current : checkpoint.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
  have budget : regularBudget checkpoint.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  obtain ⟨ready, inner, fits, clock, fields, suffixRun, suffixEq, budgetEq, credit, depth, outside⟩ :=
    OpcodeChargePrefix.normal [] checkpoint scopedPost frame (amount bytes) suffix
      (OriginalCodeEnvironment.stack_pop checkpoint.code original) (OriginalCodeEnvironment.charge_gas checkpoint.code original)
      current budget value run
  rw [fee_word bytes small] at credit
  have event : ChargeEvent checkpoint ready frame 1 (fee bytes) :=
    ⟨fits, clock, by rw [clock]; exact fields, budgetEq, credit, fee_positive bytes, outside⟩
  have finalDepth : (wordAt ready.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat := by
    simp only [List.length_nil, Nat.add_zero] at depth
    omega
  exact ⟨bytes, ready, inner, small, event.prepend before, finalDepth, suffixRun, scopeEq.trans suffixEq⟩

theorem body_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ bytes ready inner, bytes ≤ 32 ∧ ChargeEvent source ready frame 6 (fee bytes) ∧
      evaluateHOLFiniteState ready suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨bytes, ready, inner, small, event, depth, run, scopeEq⟩ := body_normal_prefix_depth source post frame installed ev cap value normal
  exact ⟨bytes, ready, inner, small, event, run, scopeEq⟩

theorem body_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 6 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ bytes ready inner, bytes ≤ 32 ∧ ChargeEvent source ready frame 6 (fee bytes) ∧
      evaluateHOLFiniteState ready suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rcases setup_exception source post frame sp installed shapes ev spMapped spCell identifier payload run with failed | prepared
  · obtain ⟨paid, bound, effect⟩ := failed
    exact Or.inl ⟨paid, by omega, effect⟩
  · obtain ⟨bytes, checkpoint, scopedPost, small, before, chargeRun, scopeEq⟩ := prepared
    have original : Input.OriginalCode.Installed checkpoint.code := by rw [before.code_eq]; exact installed
    have current : checkpoint.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
    have budget : regularBudget checkpoint.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
    have currentShape : checkpoint.eshapes.lookup (ofString "EvmErr") = some .one := by
      rw [before.eshapes_eq]
      exact shapes Input.OriginalExceptions.Kind.EvmErr
    have currentSp : checkpoint.memaddrs (frame + 16#64) := by rw [before.memaddrs_eq]; exact spMapped
    have currentGas : checkpoint.memaddrs (frame + 64#64) := by rw [before.memaddrs_eq]; exact gasMapped
    have currentUsed : checkpoint.memaddrs (frame + 184#64) := by rw [before.memaddrs_eq]; exact usedMapped
    have currentGasCell : checkpoint.memory (frame + 64#64) = .word gas :=
      (before.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
    have currentUsedCell : checkpoint.memory (frame + 184#64) = .word used := before.used.trans usedCell
    rcases OpcodeChargePrefix.exception [] (amount bytes) checkpoint scopedPost frame (wordAt checkpoint.memory (frame + 16#64)) gas used suffix
        (OriginalCodeEnvironment.stack_pop checkpoint.code original) (OriginalCodeEnvironment.charge_gas checkpoint.code original)
        current currentSp (memory_word _ _) currentGas currentUsed currentGasCell currentUsedCell budget currentShape identifier payload chargeRun with underflow | insufficient | charged
    · obtain ⟨actualId, actualPayload, impossible, effect, zero⟩ := underflow
      simp at impossible
    · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
      exact Or.inl ⟨6, Nat.le_refl _, (before.trans effect).of_emptyLocals scopeEq⟩
    · obtain ⟨ready, inner, remaining, effect, suffixRun, suffixEq⟩ := charged
      have credit := effect.used
      rw [fee_word bytes small] at credit
      have event : ChargeEvent checkpoint ready frame 1 (fee bytes) :=
        ⟨effect.fits, effect.clock, effect.fields, effect.budget, credit, fee_positive bytes, effect.outside⟩
      exact Or.inr ⟨bytes, ready, inner, small, event.prepend before, suffixRun, scopeEq.trans suffixEq⟩

end InitECandidate.Solver.GasBudget.OpcodeExp

#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.body_normal_prefix_depth
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.body_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.body_exception_prefix

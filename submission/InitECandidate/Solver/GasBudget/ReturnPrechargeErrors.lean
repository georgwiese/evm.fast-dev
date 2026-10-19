import InitECandidate.Solver.GasBudget.ReturnTailExclusions
import InitECandidate.Solver.GasBudget.StackPopsException
import InitECandidate.Solver.GasBudget.RegularChargeExceptionCall
import InitECandidate.Solver.GasBudget.PrefixEnvironment
import InitECandidate.Solver.Input.ExceptionControl

namespace InitECandidate.Solver.GasBudget.ReturnOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stack_error_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (run : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 2#64))), post)) :
    ∃ paid, paid ≤ 2 ∧ StackPop.PrefixEffect source post frame paid := by
  rw [body_shape] at run
  rcases StackPop.pops_exception ["start", "size"] source post frame sp program (OriginalCodeEnvironment.stack_pop source.code installed)
      ev mapped cell shape (ofString "EvmErr") (.val (.word 2#64)) run with underflow | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := underflow
    exact ⟨sp.toNat + 1, by simpa using bound, effect⟩
  · obtain ⟨ready, inner, remaining, effect, readyCell, depth, tailRun, scopeEq⟩ := continued
    have original : Input.OriginalCode.Installed ready.code := by rw [effect.code_eq]; exact installed
    have excluded := program_excludes ready.code original (.val (.word 2#64))
      (by simp only [ne_eq, ValueHOL.val.injEq, HolWordLab.word.injEq]; decide) ready rfl
    exact (excluded (congrArg Prod.fst tailRun)).elim

set_option maxHeartbeats 1000000 in
theorem gas_error_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (run : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 4#64))), post)) :
    ∃ paid, paid ≤ 24 ∧ StackPop.PrefixEffect source post frame paid := by
  rw [body_shape] at run
  rcases StackPop.pops_exception ["start", "size"] source post frame sp program (OriginalCodeEnvironment.stack_pop source.code installed)
      ev spMapped spCell shape (ofString "EvmErr") (.val (.word 4#64)) run with underflow | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := underflow
    have different : (.val (.word 4#64) : ValueHOL 64) ≠ .val (.word 2#64) := by
      simp only [ne_eq, ValueHOL.val.injEq, HolWordLab.word.injEq]; decide
    exact (different actualPayload).elim
  · obtain ⟨popped, scopedPost, remaining, before, poppedSP, depth, poppedRun, bodyScope⟩ := continued
    have original : Input.OriginalCode.Installed popped.code := by rw [before.code_eq]; exact installed
    obtain ⟨costPaid, x, inner, positive, bounded, funded, chargeRun, costScope⟩ := Input.PricedReadOnlyPrefix.exception
      popped scopedPost "x" (.comb [.one, .one]) (ofString "extend_memory_cost1") [localVar "start", localVar "size"] afterCost
      MemoryCostEffects.Kind.extend_memory_cost1.signature.1 MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2 20
      (MemoryCostEffects.entry popped.code original .extend_memory_cost1) (MemoryCostEffects.pure_extend_memory_cost1 popped.code original)
      (MemoryCostEffects.price_extend_memory_cost1 popped.code original) (MemoryCostEffects.safe_extend_memory_cost1 popped.code original)
      (ofString "EvmErr") (.val (.word 4#64)) poppedRun
    let first := setVarHOLFinite (ofString "x") x {popped with clock := popped.clock - costPaid}
    have costEffect : StackPop.PrefixEffect popped first frame costPaid := StackPop.PrefixEffect.unchanged popped first frame costPaid funded rfl rfl
    have totalBefore := before.trans costEffect
    have firstOriginal : Input.OriginalCode.Installed first.code := by rw [totalBefore.code_eq]; exact installed
    rcases Input.sequence_exception first inner (.call (some (none, none)) (ofString "charge_gas") [.rfield 0 (localVar "x")]) afterCharge
        (ofString "EvmErr") (.val (.word 4#64)) chargeRun with failed | continued
    · have firstEv : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [totalBefore.globals_eq]; exact ev
      have firstGas : first.memaddrs (frame + 64#64) := by rw [totalBefore.memaddrs_eq]; exact gasMapped
      have firstUsed : first.memaddrs (frame + 184#64) := by rw [totalBefore.memaddrs_eq]; exact usedMapped
      have firstGasCell := (totalBefore.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
      have firstUsedCell := totalBefore.used.trans usedCell
      have firstCap : regularBudget first.memory frame ≤ 16777216 := by rw [totalBefore.budget]; exact cap
      have firstShape : first.eshapes.lookup (ofString "EvmErr") = some .one := by rw [totalBefore.eshapes_eq]; exact shape
      obtain ⟨actualId, actualPayload, fits, innerEq, amount, unavailable, args⟩ := RegularCharge.call_exception first inner frame gas used [.rfield 0 (localVar "x")]
        (OriginalCodeEnvironment.charge_gas first.code firstOriginal) firstEv firstGas firstUsed firstGasCell firstUsedCell firstCap firstShape
        (ofString "EvmErr") (.val (.word 4#64)) failed
      have last : StackPop.PrefixEffect first inner frame 1 := StackPop.PrefixEffect.unchanged first inner frame 1 fits
        (by rw [innerEq]; rfl) (by rw [innerEq]; rfl)
      have scope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by rw [bodyScope, costScope]; rfl
      exact ⟨2 + costPaid + 1, by omega, (totalBefore.trans last).of_emptyLocals scope⟩
    · obtain ⟨charged, actualCharge, lateRun⟩ := continued
      have chargedOriginal := Input.OriginalCode.after_execution first charged _ none actualCharge firstOriginal
      have excluded := after_charge_excludes charged.code chargedOriginal (.val (.word 4#64)) charged rfl
      exact (excluded (congrArg Prod.fst lateRun)).elim

end InitECandidate.Solver.GasBudget.ReturnOpcode

#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.stack_error_prefix
#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.gas_error_prefix

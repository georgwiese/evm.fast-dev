import InitECandidate.Solver.GasBudget.OpcodeTstoreProgram
import InitECandidate.Solver.GasBudget.ChargeEvent
import InitECandidate.Solver.Input.OriginalExceptions

namespace InitECandidate.Solver.GasBudget.OpcodeTstore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ ready inner, ChargeEvent source ready frame 4 100 ∧
      evaluateHOLFiniteState ready suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at normal
  obtain ⟨positive, restRun⟩ := RequireNotStatic.normal_prefix source post _ installed value normal
  let entry := {source with clock := source.clock - 1}
  have before := StackPop.PrefixEffect.unchanged source entry frame 1 positive rfl rfl
  obtain ⟨ready, inner, fits, clock, frameEq, suffixRun, scopeEq, budget, credit, depth, outside⟩ :=
    OpcodeChargePrefix.normal names entry post frame 100#64 suffix (OriginalCodeEnvironment.stack_pop source.code installed)
      (OriginalCodeEnvironment.charge_gas source.code installed) ev cap value restRun
  have centum : (100#64 : BitVec 64).toNat = 100 := by decide
  rw [centum] at credit
  have fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {entry with memory := ready.memory, clock := ready.clock} := by rw [clock]; exact frameEq
  have event : ChargeEvent entry ready frame 3 100 := ⟨fits, clock, fields, budget, credit, by decide, outside⟩
  exact ⟨ready, inner, event.prepend before, suffixRun, scopeEq⟩

theorem body_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 4 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ ready inner, ChargeEvent source ready frame 4 100 ∧
      evaluateHOLFiniteState ready suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  rcases RequireNotStatic.exception_prefix source post _ installed identifier payload run with failed | passed
  · obtain ⟨positive, clock, fields⟩ := failed
    exact Or.inl ⟨1, by decide, StackPop.PrefixEffect.unchanged source post frame 1 positive clock fields⟩
  · obtain ⟨positive, restRun⟩ := passed
    let entry := {source with clock := source.clock - 1}
    have before := StackPop.PrefixEffect.unchanged source entry frame 1 positive rfl rfl
    rcases OpcodeChargePrefix.exception names 100#64 entry post frame sp gas used suffix
        (OriginalCodeEnvironment.stack_pop source.code installed) (OriginalCodeEnvironment.charge_gas source.code installed) ev spMapped spCell
        gasMapped usedMapped gasCell usedCell cap (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload restRun with underflow | insufficient | charged
    · obtain ⟨actualId, actualPayload, depth, effect, zeroCell⟩ := underflow
      have bound : 1 + (sp.toNat + 1) ≤ 4 := by change sp.toNat + 1 ≤ 2 at depth; omega
      exact Or.inl ⟨1 + (sp.toNat + 1), bound, before.trans effect⟩
    · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
      exact Or.inl ⟨4, Nat.le_refl _, before.trans effect⟩
    · obtain ⟨ready, inner, remaining, effect, suffixRun, scopeEq⟩ := charged
      have credit := effect.used
      have centum : (100#64 : BitVec 64).toNat = 100 := by decide
      rw [centum] at credit
      have event : ChargeEvent entry ready frame 3 100 :=
        ⟨effect.fits, effect.clock, effect.fields, effect.budget, credit, by decide, effect.outside⟩
      exact Or.inr ⟨ready, inner, event.prepend before, suffixRun, scopeEq⟩

end InitECandidate.Solver.GasBudget.OpcodeTstore

#print axioms InitECandidate.Solver.GasBudget.OpcodeTstore.body_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodeTstore.body_exception_prefix

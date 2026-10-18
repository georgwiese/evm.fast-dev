import InitECandidate.Solver.GasBudget.OpcodePushProgram
import InitECandidate.Solver.GasBudget.ChargeEvent

namespace InitECandidate.Solver.GasBudget.OpcodePush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame bytes : BitVec 64)
    (bytesLocal : source.locals.lookup (ofString "nbytes") = some (.val (.word bytes)))
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ ready inner, ChargeEvent source ready frame 1 (fee bytes) ∧
      evaluateHOLFiniteState ready suffix = (some (.returned value), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_choice source bytes bytesLocal] at normal
  obtain ⟨ready, inner, fits, clock, frameEq, suffixRun, scopeEq, budget, credit, depth, outside⟩ :=
    OpcodeChargePrefix.normal [] source post frame (amount bytes) suffix stackCode chargeCode ev cap value normal
  rw [amount_value] at credit
  have fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock} := by rw [clock]; exact frameEq
  exact ⟨ready, inner, ⟨fits, clock, fields, budget, credit, fee_positive bytes, outside⟩, suffixRun, scopeEq⟩

theorem body_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used bytes : BitVec 64)
    (bytesLocal : source.locals.lookup (ofString "nbytes") = some (.val (.word bytes)))
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ gas < amount bytes ∧ StackPop.PrefixEffect source post frame 1) ∨
    ∃ ready inner, ChargeEvent source ready frame 1 (fee bytes) ∧
      evaluateHOLFiniteState ready suffix = (some (.exception identifier payload), inner) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_choice source bytes bytesLocal] at run
  rcases OpcodeChargePrefix.exception [] (amount bytes) source post frame sp gas used suffix stackCode chargeCode ev
      spMapped spCell gasMapped usedMapped gasCell usedCell cap exceptionShape identifier payload run with underflow | insufficient | charged
  · obtain ⟨actualId, actualPayload, impossible, effect, cell⟩ := underflow
    simp at impossible
  · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
    exact Or.inl ⟨actualId, actualPayload, unavailable, effect⟩
  · obtain ⟨ready, inner, remaining, effect, suffixRun, scopeEq⟩ := charged
    have credit := effect.used
    rw [amount_value] at credit
    exact Or.inr ⟨ready, inner, ⟨effect.fits, effect.clock, effect.fields, effect.budget, credit, fee_positive bytes, effect.outside⟩, suffixRun, scopeEq⟩

end InitECandidate.Solver.GasBudget.OpcodePush

#print axioms InitECandidate.Solver.GasBudget.OpcodePush.body_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.body_exception_prefix

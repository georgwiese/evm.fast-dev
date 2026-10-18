import InitECandidate.Solver.GasBudget.OpcodeChargeException
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.OpcodeChargeSites
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All59 original positive-charge sites, on their actual exceptional paths.
Every uncovered suffix remains the genuine original suffix; only its entry
effects are asserted. Underflow/out-of-gas exits are derived before that suffix. -/
theorem exception (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source kind.body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ sp.toNat + 1 ≤ kind.names.length ∧
      StackPop.PrefixEffect source post frame (sp.toNat + 1) ∧ post.memory (frame + 16#64) = .word 0#64) ∨
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ kind.names.length ≤ sp.toNat ∧ gas < BitVec.ofNat 64 kind.fee ∧
      StackPop.PrefixEffect source post frame (kind.names.length + 1)) ∨
    ∃ ready inner remaining,
      OpcodeChargePrefix.ChargedEffect source ready frame sp remaining kind.names.length (BitVec.ofNat 64 kind.fee) ∧
      (wordAt source.memory (frame + 184#64)).toNat < (wordAt ready.memory (frame + 184#64)).toNat ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  rcases OpcodeChargePrefix.exception kind.names (BitVec.ofNat 64 kind.fee) source post frame sp gas used kind.suffix stackCode chargeCode ev
      spMapped spCell gasMapped usedMapped gasCell usedCell cap exceptionShape identifier payload run with underflow | insufficient | charged
  · exact Or.inl underflow
  · exact Or.inr (Or.inl insufficient)
  · obtain ⟨ready, inner, remaining, effect, restRun, scopeEq⟩ := charged
    have credit := effect.used
    have positive := fee_positive kind
    exact Or.inr (Or.inr ⟨ready, inner, remaining, effect, by omega, restRun, scopeEq⟩)

end InitECandidate.Solver.GasBudget.OpcodeChargeSites

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.exception

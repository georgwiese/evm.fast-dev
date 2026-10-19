import InitECandidate.Solver.GasBudget.ForwardCalculator
import InitECandidate.Solver.GasBudget.ForwardFrameSums

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem calculator_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used requested : BitVec 64) (words : U256Zero.Quad) (ancestors : List (BitVec 64))
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (apart : FrameSums.Outside frame ancestors)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (gasCell : source.memory (frame + 64#64) = .word left) (usedCell : source.memory (frame + 184#64) = .word used)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (CallGas.values words requested left))
    (calculatorCode : source.code.lookup (ofString "calculate_message_call_gas") = some (CallGas.formals, CallGas.body, CallGas.returnShape))
    (zeroCode : source.code.lookup (ofString "u256_is_zero") = some (U256Zero.formals, U256Zero.body, .one))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216) (funded : CallGas.stipend words ≤ used)
    (run : evaluateHOLFiniteState source (calculatorProgram arguments continuation) = (some (.returned returned), post)) :
    ∃ ready inner, 4 ≤ source.clock ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 4} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source "mcg" inner ∧
      FrameSums.budget ready.memory (frame :: ancestors) + (CallGas.capped requested left + CallGas.stipend words).toNat = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used ready.memory (frame :: ancestors) + (CallGas.stipend words).toNat = FrameSums.used source.memory (frame :: ancestors) := by
  obtain ⟨ready, inner, fits, fields, tailRun, scope, budget, usedReady, gasReady, debit, outside, locals⟩ :=
    calculator_normal source post frame left used requested words arguments continuation returned ev gasCell usedCell args calculatorCode zeroCode addCode chargeCode cap funded run
  obtain ⟨ancestorBudget, ancestorUsed⟩ := FrameSums.outside_preserved source.memory ready.memory frame ancestors apart outside
  refine ⟨ready, inner, fits, fields, tailRun, scope, ?_, ?_⟩
  · change regularBudget ready.memory frame + FrameSums.budget ready.memory ancestors + _ = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [ancestorBudget]
    omega
  · change (wordAt ready.memory (frame + 184#64)).toNat + FrameSums.used ready.memory ancestors + _ =
      (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors
    have sourceUsed : (wordAt source.memory (frame + 184#64)).toNat = used.toNat := by
      simp only [wordAt, usedCell, WitnessRadix.MemoryBytes.wordBits]
    rw [ancestorUsed, sourceUsed]
    omega

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.calculator_sums

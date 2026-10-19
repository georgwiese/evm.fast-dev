import InitECandidate.Solver.GasBudget.CallGasNormal
import InitECandidate.Solver.GasBudget.ForwardPrefixNormal

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def calculatorProgram (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "mcg") CallGas.returnShape (ofString "calculate_message_call_gas") arguments (program continuation)

/-- Real calculator, charge and counter debit compose in four source clocks.
The future continuation is extracted from the original successful run, and
the forwarded child seed is removed exactly once from the parent ledger. -/
theorem calculator_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used requested : BitVec 64) (words : U256Zero.Quad)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
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
      regularBudget ready.memory frame + (CallGas.capped requested left + CallGas.stipend words).toNat = regularBudget source.memory frame ∧
      ready.memory (frame + 184#64) = .word (used - CallGas.stipend words) ∧
      ready.memory (frame + 64#64) = .word (left - CallGas.capped requested left) ∧
      (wordAt ready.memory (frame + 184#64)).toNat + (CallGas.stipend words).toNat = used.toNat ∧
      (∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → ready.memory address = source.memory address) ∧
      ready.locals = (CallGas.callerPost source "mcg" (CallGas.capped requested left) (CallGas.capped requested left + CallGas.stipend words)).locals := by
  obtain ⟨calculatorFits, result, forwardRun, scope⟩ := CallGas.call_normal source post words requested left "mcg" arguments (program continuation) returned
    args calculatorCode zeroCode addCode run
  let calculated := CallGas.callerPost source "mcg" (CallGas.capped requested left) (CallGas.capped requested left + CallGas.stipend words)
  have binding : calculated.locals.lookup (ofString "mcg") = some (CallGas.pair (CallGas.capped requested left) (CallGas.capped requested left + CallGas.stipend words)) := by
    simp [calculated, CallGas.callerPost, setVarHOLFinite, HolFiniteMapExact.updateEq, FUPDATE, FUPDATE_HOL]
  obtain ⟨ready, forwardFits, canonical, tailRun, budget, usedReady, gasReady, debit, outside⟩ :=
    normal calculated result frame left used requested words ev binding gasCell usedCell chargeCode cap funded continuation returned forwardRun
  have fields := congrArg emptyLocalsHOLFinite canonical
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 3 - 1} at fields
  have subtraction : source.clock - 3 - 1 = source.clock - 4 := by omega
  rw [subtraction] at fields
  change 1 ≤ source.clock - 3 at forwardFits
  have locals := congrArg PanSemStateFiniteExact.locals canonical
  exact ⟨ready, result, by omega, fields, tailRun, scope, budget, usedReady, gasReady, debit, outside, locals⟩

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.calculator_normal

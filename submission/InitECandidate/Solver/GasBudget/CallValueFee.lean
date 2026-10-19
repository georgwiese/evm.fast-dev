import InitECandidate.Solver.GasBudget.ForwardMemoryCredit
import InitECandidate.Solver.GasBudget.SaturatingAddPrefix
import InitECandidate.Solver.GasBudget.RegularChargeMemory
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.GasBudget.CallValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def feeExpression : ExpHOL 64 := .op .add [localVar "access_cost", localVar "transfer_cost"]
def afterFee (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "charge_gas") [localVar "need"]) continuation
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "need") .one (ofString "add_sat") [feeExpression, .rfield 0 (localVar "x")] (afterFee continuation)

/-- The actual add_sat and first CALL/CALLCODE charge determine the fee,
affordability, stipend funding and memory surplus. No later gas credit or
successful helper run is a premise. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame access memoryCost expand : BitVec 64) (words : U256Zero.Quad)
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (accessCell : source.locals.lookup (ofString "access_cost") = some (.val (.word access)))
    (transferCell : source.locals.lookup (ofString "transfer_cost") = some (.val (.word (ForwardCredit.valueFee words))))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (run : evaluateHOLFiniteState source (program continuation) = (some (.returned returned), post)) :
    ∃ ready inner, 2 ≤ source.clock ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 2} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source "need" inner ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost).toNat ∧
      memoryCost.toNat + (CallGas.stipend words).toNat + 100 ≤
        (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost).toNat ∧
      (∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → ready.memory address = source.memory address) ∧
      ready.locals = (bind {source with clock := source.clock - 1} "need"
        (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost)).locals := by
  obtain ⟨a, b, inner, addFits, actualArgs, lower, chargeRun, scope⟩ :=
    SaturatingAdd.normal_prefix source post "need" [feeExpression, .rfield 0 (localVar "x")] (afterFee continuation) addCode returned run
  have expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [feeExpression, .rfield 0 (localVar "x")] =
      some [.val (.word (access + ForwardCredit.valueFee words)), .val (.word memoryCost)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, feeExpression, localVar, accessCell, transferCell, xCell,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have valuesEq := Option.some.inj (actualArgs.symm.trans expectedArgs)
  have identified : a = access + ForwardCredit.valueFee words ∧ b = memoryCost := by simpa using valuesEq
  obtain ⟨aEq, bEq⟩ := identified
  subst a
  subst b
  let amount := SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost
  let first := bind {source with clock := source.clock - 1} "need" amount
  have needCell : first.locals.lookup (ofString "need") = some (.val (.word amount)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [localVar "need"] = some [.val (.word amount)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, needCell]
  have safe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "charge_gas") [localVar "need"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨ready, actualCharge, tailRun, saved⟩ := safe.normal_continue first inner continuation returned chargeRun
  obtain ⟨gas, used, chargeFits, clock, gasMapped, usedMapped, gasCell, usedCell, affordable, canonical, budget, debit, credit⟩ :=
    RegularCharge.call_normal first ready frame amount [localVar "need"] args chargeCode ev cap actualCharge
  have oldUsed : (wordAt source.memory (frame + 184#64)).toNat = used.toNat := by
    change (wordAt first.memory (frame + 184#64)).toNat = used.toNat
    simp only [wordAt, usedCell, WitnessRadix.MemoryBytes.wordBits]
  have gasBound : gas.toNat ≤ 16777216 := by
    change regularBudget first.memory frame ≤ 16777216 at cap
    unfold regularBudget at cap
    simp only [wordAt, gasCell, WitnessRadix.MemoryBytes.wordBits] at cap
    omega
  have amountBound : amount.toNat ≤ 16777216 := (show amount.toNat ≤ gas.toNat from affordable).trans gasBound
  have surplus := ForwardCredit.memory_surplus words access memoryCost accessLower accessUpper amountBound
  have fields := congrArg emptyLocalsHOLFinite canonical
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 1 - 1} at fields
  have subtraction : source.clock - 1 - 1 = source.clock - 2 := by omega
  rw [subtraction] at fields
  change 1 ≤ source.clock - 1 at chargeFits
  have locals := congrArg PanSemStateFiniteExact.locals canonical
  refine ⟨ready, inner, by omega, fields, tailRun, scope, budget, by rw [oldUsed]; exact credit, surplus, ?_, locals⟩
  intro address notGas notUsed
  exact RegularCharge.call_other_word first ready frame amount address [localVar "need"] args chargeCode ev cap actualCharge notGas notUsed

end InitECandidate.Solver.GasBudget.CallValueFee

#print axioms InitECandidate.Solver.GasBudget.CallValueFee.normal

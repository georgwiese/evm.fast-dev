import InitECandidate.Solver.GasBudget.CallValueFee
import InitECandidate.Solver.GasBudget.RegularChargeExceptionCall
import InitECandidate.Solver.Input.ExceptionControl
import InitECandidate.Solver.GasBudget.ChargeEvent

namespace InitECandidate.Solver.GasBudget.CallValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 2000000 in
/-- Escaping exceptions locate a real failed first charge or a genuine
successful charge followed by the actual exceptional suffix. -/
theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame access memoryCost expand gas used : BitVec 64) (words : U256Zero.Quad)
    (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (accessCell : source.locals.lookup (ofString "access_cost") = some (.val (.word access)))
    (transferCell : source.locals.lookup (ofString "transfer_cost") = some (.val (.word (ForwardCredit.valueFee words))))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (run : evaluateHOLFiniteState source (program continuation) = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ StackPop.PrefixEffect source post frame 2) ∨
    ∃ ready inner, ChargeEvent source ready frame 2 (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost).toNat ∧
      memoryCost.toNat + (CallGas.stipend words).toNat + 100 ≤ (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost).toNat ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source "need" inner ∧
      ready.locals = (bind {source with clock := source.clock - 1} "need"
        (SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost)).locals := by
  obtain ⟨a, b, inner, addFits, actualArgs, lower, chargeRun, scope⟩ :=
    SaturatingAdd.exception_prefix source post "need" [feeExpression, .rfield 0 (localVar "x")] (afterFee continuation) addCode identifier payload run
  have expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [feeExpression, .rfield 0 (localVar "x")] = some [.val (.word (access + ForwardCredit.valueFee words)), .val (.word memoryCost)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, feeExpression, localVar, accessCell, transferCell, xCell,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have identified : a = access + ForwardCredit.valueFee words ∧ b = memoryCost := by
    have same := Option.some.inj (actualArgs.symm.trans expectedArgs)
    simpa using same
  obtain ⟨aEq, bEq⟩ := identified
  subst a
  subst b
  let amount := SaturatingAdd.resultWord (access + ForwardCredit.valueFee words) memoryCost
  let first := bind {source with clock := source.clock - 1} "need" amount
  have needCell : first.locals.lookup (ofString "need") = some (.val (.word amount)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [localVar "need"] = some [.val (.word amount)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, needCell]
  rcases Input.sequence_exception first inner (.call (some (none, none)) (ofString "charge_gas") [localVar "need"]) continuation identifier payload chargeRun with failed | continued
  · obtain ⟨actualId, actualPayload, funded, innerEq, actualAmount, unavailable, actualRead⟩ :=
      RegularCharge.call_exception first inner frame gas used [localVar "need"] chargeCode ev gasMapped usedMapped gasCell usedCell cap shape identifier payload failed
    have before : StackPop.PrefixEffect source first frame 1 := StackPop.PrefixEffect.unchanged source first frame 1 addFits rfl rfl
    have after : StackPop.PrefixEffect first inner frame 1 := StackPop.PrefixEffect.unchanged first inner frame 1 funded
      (by rw [innerEq]; rfl) (by rw [innerEq]; rfl)
    exact Or.inl ⟨actualId, actualPayload, (before.trans after).of_emptyLocals (by rw [scope]; rfl)⟩
  · obtain ⟨ready, actualCharge, tailRun⟩ := continued
    obtain ⟨actualGas, actualUsed, chargeFits, clock, mappedGas, mappedUsed, currentGas, currentUsed, affordable, canonical, budget, debit, credit⟩ :=
      RegularCharge.call_normal first ready frame amount [localVar "need"] args chargeCode ev cap actualCharge
    have oldUsed : (wordAt source.memory (frame + 184#64)).toNat = actualUsed.toNat := by
      change (wordAt first.memory (frame + 184#64)).toNat = actualUsed.toNat
      simp only [wordAt, currentUsed, WitnessRadix.MemoryBytes.wordBits]
    have gasBound : actualGas.toNat ≤ 16777216 := by
      change regularBudget first.memory frame ≤ 16777216 at cap
      unfold regularBudget at cap
      simp only [wordAt, currentGas, WitnessRadix.MemoryBytes.wordBits] at cap
      omega
    have amountBound : amount.toNat ≤ 16777216 := (show amount.toNat ≤ actualGas.toNat from affordable).trans gasBound
    have surplus := ForwardCredit.memory_surplus words access memoryCost accessLower accessUpper amountBound
    have fields := congrArg emptyLocalsHOLFinite canonical
    change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 1 - 1} at fields
    have subtraction : source.clock - 1 - 1 = source.clock - 2 := by omega
    rw [subtraction] at fields
    have readyClock : ready.clock = source.clock - 2 := by rw [clock]; exact subtraction
    change 1 ≤ source.clock - 1 at chargeFits
    have locals := congrArg PanSemStateFiniteExact.locals canonical
    refine Or.inr ⟨ready, inner, ?_, surplus, tailRun, scope, locals⟩
    refine ⟨by omega, readyClock, by rw [readyClock]; exact fields, budget, by rw [oldUsed]; exact credit, by omega, ?_⟩
    intro address notSP notGas notUsed
    exact RegularCharge.call_other_word first ready frame amount address [localVar "need"] args chargeCode ev cap actualCharge notGas notUsed

end InitECandidate.Solver.GasBudget.CallValueFee

#print axioms InitECandidate.Solver.GasBudget.CallValueFee.exception_prefix

import InitECandidate.Solver.GasBudget.RegularChargeOutcomes
import InitECandidate.Solver.Input.IgnoredCallException
import InitECandidate.Solver.Input.UnaryCallData
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual charging exception recovers its real scalar argument and
derives the exact unchanged-memory caller state and its one paid clock. -/
theorem call_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame gas used : BitVec 64) (arguments : List (ExpHOL 64))
    (code : source.code.lookup (ofString "charge_gas") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") arguments) = (some (.exception identifier payload), post)) :
    identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ 1 ≤ source.clock ∧
      post = emptyLocalsHOLFinite {source with clock := source.clock - 1} ∧
      ∃ amount : BitVec 64, gas < amount ∧
        evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)] := by
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "charge_gas") arguments identifier payload normal
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "charge_gas") (ofString "amount") .one body .one code values actual callee returnShape called
  obtain ⟨amount, argumentEq⟩ := Input.RlpWrite.U256Value.scalar_word argument typed
  rw [argumentEq] at binding valuesEq
  rw [bodyEq] at bodyRun
  rw [valuesEq] at args
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨actualPost, actualRun, actualFrame, actualClock, budget, credit, debit, away⟩ := body_outcomes entry frame gas used amount ev binding
    gasMapped usedMapped gasCell usedCell cap shape
  have sameResult := congrArg Prod.fst (bodyRun.symm.trans actualRun)
  have unavailable : ¬ amount ≤ gas := by
    intro affordable
    simp only [outcome, if_pos affordable] at sameResult
    cases sameResult
  have ids : identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) := by
    simpa only [outcome, if_neg unavailable, Option.some.injEq, PanSemResultExact.exception.injEq] using sameResult
  have actualCaller := failed_call source frame gas amount arguments args code ev gasMapped gasCell
    (show gas < amount by change ¬ amount.toNat ≤ gas.toNat at unavailable; change gas.toNat < amount.toNat; omega) shape positive
  rw [ids.1, ids.2] at normal
  have finalEq : post = emptyLocalsHOLFinite {source with clock := source.clock - 1} := congrArg Prod.snd (normal.symm.trans actualCaller)
  exact ⟨ids.1, ids.2, positive, finalEq, amount, by change ¬ amount.toNat ≤ gas.toNat at unavailable; change gas.toNat < amount.toNat; omega, args⟩

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.call_exception

import InitECandidate.Solver.GasBudget.RegularChargeNormal
import InitECandidate.Solver.Input.ScalarNormal

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal charge execution derives both frame-cell mappings and
the old word values, then its guard proves affordability. The only saved
data inputs are the current ev and amount bindings. -/
theorem normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ gas used : BitVec 64,
      source.memaddrs (frame + 64#64) ∧ source.memaddrs (frame + 184#64) ∧
      source.memory (frame + 64#64) = .word gas ∧ source.memory (frame + 184#64) = .word used ∧ amount ≤ gas := by
  have expanded := normal
  rw [body_shape] at expanded
  obtain ⟨declared, inner, read, _, innerRun, restored⟩ := Input.CallNormal.declaration_normal_entry source post "gl" .one (frameLoad 64#64) tail value expanded
  have gasMapped := Input.load_one_mapped source (frameAddress 64#64) (frame + 64#64) declared (address_read source frame 64#64 ev) read
  cases gasCell : source.memory (frame + 64#64) with
  | word gas =>
    have gasRead := frame_read source frame 64#64 gas ev gasMapped gasCell
    have same : declared = .val (.word gas) := Option.some.inj (read.symm.trans gasRead)
    subst declared
    let entered := bind source "gl" gas
    have guardSafe : Input.PureGuard guard := .ite _ (.raise _ _) .skip
    have afterGuardRun := guardSafe.normal_continue entered inner afterGuard value innerRun
    have safe : Input.LocalPrefix (ofString "amount") (.store (frameAddress 64#64) gasExpression) := .store _ _
    obtain ⟨first, firstRun, firstRest, _⟩ := safe.normal_continue entered inner _ value afterGuardRun
    have firstFrame := Input.store_none_frame entered first _ _ firstRun
    have firstEV : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstFrame]; exact ev
    have secondSafe : Input.LocalPrefix (ofString "amount") (.store (frameAddress 184#64) usedExpression) := .store _ _
    obtain ⟨second, secondRun, returnRun, _⟩ := secondSafe.normal_continue first inner _ value firstRest
    have usedMapped : first.memaddrs (frame + 184#64) := Input.store_mapped_normal first second _ usedExpression _
      (address_read first frame 184#64 firstEV)
      (by intro actual observed; have length := Input.op_length first .add [frameLoad 184#64, localVar "amount"] actual observed; omega) secondRun
    have sourceUsedMapped : source.memaddrs (frame + 184#64) := by rw [firstFrame] at usedMapped; exact usedMapped
    cases usedCell : source.memory (frame + 184#64) with
    | word used => exact ⟨gas, used, gasMapped, sourceUsedMapped, rfl, rfl, normal_affordable source post frame gas amount ev amountLocal gasMapped gasCell value normal⟩

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.normal_entry

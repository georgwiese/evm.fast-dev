import InitECandidate.Solver.GasBudget.RegularChargeCall
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal charge derives affordability from the actual original
guard, independently of exception-shape validity or caller clock funding. -/
theorem normal_affordable (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (gasMapped : source.memaddrs (frame + 64#64)) (gasCell : source.memory (frame + 64#64) = .word gas)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) : amount ≤ gas := by
  rw [body_shape] at normal
  obtain ⟨declared, inner, read, _, innerRun, restored⟩ := Input.CallNormal.declaration_normal_entry source post "gl" .one (frameLoad 64#64) tail value normal
  have gasRead := frame_read source frame 64#64 gas ev gasMapped gasCell
  have same : declared = .val (.word gas) := Option.some.inj (read.symm.trans gasRead)
  subst declared
  let entered := bind source "gl" gas
  have glLocal : entered.locals.lookup (ofString "gl") = some (.val (.word gas)) := bind_lookup_same _ _ _
  have enteredAmount : entered.locals.lookup (ofString "amount") = some (.val (.word amount)) := (bind_lookup_other _ "gl" "amount" _ (by decide)).trans amountLocal
  have guardSafe : Input.PureGuard guard := .ite _ (.raise _ _) .skip
  have passed := guardSafe.normal_passed entered inner afterGuard value innerRun
  by_contra unavailable
  have bad : gas < amount := by change ¬amount.toNat ≤ gas.toNat at unavailable; change gas.toNat < amount.toNat; omega
  have selected : evaluateHOLFiniteState entered guard = evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 4#64)) := by
    rw [guard, evaluateHOLFiniteState_ite]
    simp [test, evalHOLExact, evalListHOLExact, toExact, localVar, glLocal, enteredAmount, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
  exact Input.raise_ne_none entered (ofString "EvmErr") (.const 4#64) (congrArg Prod.fst (selected.symm.trans passed))

/-- The physical capped regular ledger supplies the addition bound needed
to interpret real gas/used updates as natural numbers without wrap. -/
theorem ledger_fits (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used : BitVec 64)
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216) : gas.toNat + used.toNat < 2 ^ 64 := by
  simp only [regularBudget, wordAt, gasCell, usedCell, WitnessRadix.MemoryBytes.wordBits] at cap
  omega

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.normal_affordable
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.ledger_fits

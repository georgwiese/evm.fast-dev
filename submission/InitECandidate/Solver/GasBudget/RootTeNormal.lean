import InitECandidate.Solver.GasBudget.RootTeProgram
import InitECandidate.Solver.Input.NormalScalarStore

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From the actual post-split transaction continuation, reach and execute
TE_GAS with its capped original mgas. The helper returns, TE pointer, destination
mapping and intervening stores follow from normal execution. No cost or later
TE/message memory preservation is asserted here. -/
theorem normal_te_gas (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (gas : BitVec 64) (intrinsicRegular : Nat)
    (gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas)))
    (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (run : evaluateHOLFiniteState source afterSplit = (some (.returned value), post)) :
    ∃ (ready stored finish : PanSemStateFiniteExact 64 Guest.HostMemory) (te : BitVec 64),
      evaluateHOLFiniteState ready teGasSite = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "te") = some (.val (.word te)) ∧
      ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) ∧
      ready.memaddrs (te + 80#64) ∧
      evaluateHOLFiniteState ready teGasStore = (none, stored) ∧
      evaluateHOLFiniteState stored afterTeGas = (some (.returned value), finish) ∧
      stored.memory (te + 80#64) = .word gas ∧
      (wordAt stored.memory (te + 80#64)).toNat + intrinsicRegular ≤ 16777216 ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  rw [actual_before_te_gas] at run
  obtain ⟨ready, finish, siteRun, localEq, codes, shapes⟩ :=
    (te_gas_path teGasSite).normal_reaches source post value run
  have readyGas : ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) := localEq.trans gasLocal
  have splitRun := siteRun
  rw [actual_te_gas] at splitRun
  obtain ⟨stored, storeRun, restRun, localsEq⟩ :=
    (Input.LocalPrefix.store (key := ofString "mgas") _ _).normal_continue ready finish afterTeGas value splitRun
  obtain ⟨te, teLocal, mapped, postEq, gasCell⟩ := Input.scalar_store_normal ready stored "te" "mgas" 80#64 gas readyGas storeRun
  refine ⟨ready, stored, finish, te, siteRun, teLocal, readyGas, mapped, storeRun, restRun, gasCell, ?_, codes, shapes⟩
  simpa [wordAt, gasCell, WitnessRadix.MemoryBytes.wordBits] using cap

/-- Actual validator, complete caller through its real split, balance setup,
TE allocation and TE_GAS store. The physical TE word and intrinsic regular
component obey the validator's cap. This is normal-path reachability only. -/
theorem validated_te_gas (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (validator : source.code.lookup (ofString "validate_transaction") = some (RootValidation.validationFormals, RootValidation.body, RootValidation.intrinsicShape))
    (minimum : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (txError : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source validationCall = (some (.returned value), post)) :
    ∃ (ready stored finish : PanSemStateFiniteExact 64 Guest.HostMemory) (te gas regular : BitVec 64),
      evaluateHOLFiniteState ready teGasSite = (some (.returned value), finish) ∧
      evaluateHOLFiniteState ready teGasStore = (none, stored) ∧
      evaluateHOLFiniteState stored afterTeGas = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "te") = some (.val (.word te)) ∧
      stored.memory (te + 80#64) = .word gas ∧
      gas.toNat + regular.toNat ≤ 16777216 ∧
      (wordAt stored.memory (te + 80#64)).toNat + regular.toNat ≤ 16777216 ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  obtain ⟨splitSource, splitPost, txGas, intrinsic, regular, state, floor, suffixRun, cap, floorCap,
    gasLocal, reservoirLocal, intrinsicLocal, codes, shapes⟩ := normal_root source post value validator minimum txError run
  obtain ⟨ready, stored, finish, te, siteRun, teLocal, readyGas, mapped, storeRun, restRun, gasCell, storedCap, readyCodes, readyShapes⟩ :=
    normal_te_gas _ splitPost value (RootBudget.liquidWord txGas intrinsic regular) regular.toNat gasLocal cap suffixRun
  exact ⟨ready, stored, finish, te, RootBudget.liquidWord txGas intrinsic regular, regular,
    siteRun, storeRun, restRun, teLocal, gasCell, cap, storedCap, readyCodes.trans codes, readyShapes.trans shapes⟩

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.normal_te_gas
#print axioms InitECandidate.Solver.GasBudget.RootCaller.validated_te_gas

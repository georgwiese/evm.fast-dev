import InitECandidate.Solver.GasBudget.RootMsgProgram
import InitECandidate.Solver.Input.NormalScalarStore

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From the actual post-split transaction continuation, reach and execute
MSG_GAS with its capped original mgas. The helper returns, message pointer, destination
mapping and intervening stores follow from normal execution. No cost or later
message memory preservation is asserted here. -/
theorem normal_msg_gas (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (gas : BitVec 64) (intrinsicRegular : Nat)
    (gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas)))
    (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (run : evaluateHOLFiniteState source afterSplit = (some (.returned value), post)) :
    ∃ (ready stored finish : PanSemStateFiniteExact 64 Guest.HostMemory) (message : BitVec 64),
      evaluateHOLFiniteState ready msgGasSite = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "m") = some (.val (.word message)) ∧
      ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) ∧
      ready.memaddrs (message + 40#64) ∧
      evaluateHOLFiniteState ready msgGasStore = (none, stored) ∧
      evaluateHOLFiniteState stored afterMsgGas = (some (.returned value), finish) ∧
      stored.memory (message + 40#64) = .word gas ∧
      (wordAt stored.memory (message + 40#64)).toNat + intrinsicRegular ≤ 16777216 ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  obtain ⟨ready, finish, siteRun, localEq, codes, shapes⟩ :=
    msg_gas_path.normal_reaches source post value run
  have readyGas : ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) := localEq.trans gasLocal
  have splitRun := siteRun
  rw [actual_msg_gas] at splitRun
  obtain ⟨stored, storeRun, restRun, localsEq⟩ :=
    (Input.LocalPrefix.store (key := ofString "mgas") _ _).normal_continue ready finish afterMsgGas value splitRun
  obtain ⟨message, messageLocal, mapped, postEq, gasCell⟩ := Input.scalar_store_normal ready stored "m" "mgas" 40#64 gas readyGas storeRun
  refine ⟨ready, stored, finish, message, siteRun, messageLocal, readyGas, mapped, storeRun, restRun, gasCell, ?_, codes, shapes⟩
  simpa [wordAt, gasCell, WitnessRadix.MemoryBytes.wordBits] using cap

/-- Actual validator, complete caller through its real split, balance setup, access-list loops and
message allocation and MSG_GAS store. The physical message word and intrinsic regular
component obey the validator's cap. This is normal-path reachability only. -/
theorem validated_msg_gas (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (validator : source.code.lookup (ofString "validate_transaction") = some (RootValidation.validationFormals, RootValidation.body, RootValidation.intrinsicShape))
    (minimum : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (txError : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source validationCall = (some (.returned value), post)) :
    ∃ (ready stored finish : PanSemStateFiniteExact 64 Guest.HostMemory) (message gas regular : BitVec 64),
      evaluateHOLFiniteState ready msgGasSite = (some (.returned value), finish) ∧
      evaluateHOLFiniteState ready msgGasStore = (none, stored) ∧
      evaluateHOLFiniteState stored afterMsgGas = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "m") = some (.val (.word message)) ∧
      stored.memory (message + 40#64) = .word gas ∧
      gas.toNat + regular.toNat ≤ 16777216 ∧
      (wordAt stored.memory (message + 40#64)).toNat + regular.toNat ≤ 16777216 ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  obtain ⟨splitSource, splitPost, txGas, intrinsic, regular, state, floor, suffixRun, cap, floorCap,
    gasLocal, reservoirLocal, intrinsicLocal, codes, shapes⟩ := normal_root source post value validator minimum txError run
  obtain ⟨ready, stored, finish, message, siteRun, messageLocal, readyGas, mapped, storeRun, restRun, gasCell, storedCap, readyCodes, readyShapes⟩ :=
    normal_msg_gas _ splitPost value (RootBudget.liquidWord txGas intrinsic regular) regular.toNat gasLocal cap suffixRun
  exact ⟨ready, stored, finish, message, RootBudget.liquidWord txGas intrinsic regular, regular,
    siteRun, storeRun, restRun, messageLocal, gasCell, cap, storedCap, readyCodes.trans codes, readyShapes.trans shapes⟩

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.normal_msg_gas
#print axioms InitECandidate.Solver.GasBudget.RootCaller.validated_msg_gas

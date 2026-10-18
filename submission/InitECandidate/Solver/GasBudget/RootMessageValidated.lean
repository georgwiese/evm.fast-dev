import InitECandidate.Solver.GasBudget.RootMessageInitialProgram
import InitECandidate.Solver.GasBudget.RootCallerNormal
import InitECandidate.Solver.Input.LocalPairPath

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
/-- Both saved gas words reach the same actual message-allocation state. -/
theorem initial_pair_path : LocalPairPath "mgas" "reservoir" initialSite RootCaller.afterSplit := by
  simp only [initialSite, initialSites, RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  prove_local_pair_path

/-- The unchanged validator and full original preprocessing reach the
actual msg_new caller with both original gas words and the validator cap.
No intrinsic value, gas read, helper success or clock allowance is assumed.
Input/heap geometry and the preprocessing price remain separate obligations. -/
theorem validated_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (validator : source.code.lookup (ofString "validate_transaction") = some (RootValidation.validationFormals, RootValidation.body, RootValidation.intrinsicShape))
    (minimum : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (txError : source.eshapes.lookup (ofString "TxErr") = some .one)
    (normal : evaluateHOLFiniteState source RootCaller.validationCall = (some (.returned value), post)) :
    ∃ (ready finish : PanSemStateFiniteExact 64 Guest.HostMemory) (gas reservoir regular : BitVec 64),
      evaluateHOLFiniteState ready initialSite = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) ∧
      ready.locals.lookup (ofString "reservoir") = some (.val (.word reservoir)) ∧
      gas.toNat + regular.toNat ≤ 16777216 ∧ ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  obtain ⟨splitSource, splitPost, gas, intrinsic, regular, state, floor, suffixRun, cap, floorCap, gasLocal, reservoirLocal, stored, codes, shapes⟩ :=
    RootCaller.normal_root source post value validator minimum txError normal
  obtain ⟨ready, finish, siteRun, savedGas, savedReservoir, entryCodes, entryShapes⟩ :=
    initial_pair_path.normal_reaches (RootBudget.entered splitSource gas intrinsic regular) splitPost value suffixRun
  exact ⟨ready, finish, RootBudget.liquidWord gas intrinsic regular, RootBudget.reservoirWord gas intrinsic regular, regular,
    siteRun, savedGas.trans gasLocal, savedReservoir.trans reservoirLocal, cap, entryCodes.trans codes, entryShapes.trans shapes⟩

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.initial_pair_path
#print axioms InitECandidate.Solver.GasBudget.RootMessage.validated_entry

import InitECandidate.Solver.GasBudget.WarmAddressesProgram
import InitECandidate.Solver.GasBudget.WarmKeysConstructorProgram

namespace InitECandidate.Solver.GasBudget.WarmTables
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
/-- The exact original account-warming continuation enters the original
storage-table constructor after its literal skip. -/
theorem storage_entry : WarmAddresses.afterLoop = .seq .skip WarmKeys.constructorSite := by
  simp only [WarmAddresses.afterLoop, WarmAddresses.site, WarmAddresses.sites, WarmPrecompiles.afterLoop,
    WarmPrecompiles.site, WarmPrecompiles.sites, WarmKeys.constructorSite, WarmKeys.constructorSites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  rfl

end InitECandidate.Solver.GasBudget.WarmTables

#print axioms InitECandidate.Solver.GasBudget.WarmTables.storage_entry

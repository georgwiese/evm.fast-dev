import InitECandidate.Solver.GasBudget.WarmKeysReach

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

def resetIndex : ProgHOL 64 := .assign .local (ofString "i") (.const 0#64)
def newArguments : List (ExpHOL 64) := [.const 52#64, .const 16#64]
def constructorSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall name shape function arguments rest) =>
      (if name = ofString "ak" ∧ function = ofString "htab_new" then [code] else []) ++ constructorSites rest
  | .seq first second | .ite _ first second => constructorSites first ++ constructorSites second
  | .dec _ _ _ rest | .while _ rest => constructorSites rest
  | _ => []
def constructorSite : ProgHOL 64 := ((constructorSites RootCaller.afterMsgGas)[0]?).getD .skip

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem constructor_shape : constructorSite = .decCall (ofString "ak") .one (ofString "htab_new") newArguments (.seq resetIndex site) := by
  simp only [constructorSite, constructorSites, site, sites, RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some, newArguments, resetIndex]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem constructor_path : LocalPath "m" constructorSite RootCaller.afterMsgGas := by
  simp only [constructorSite, constructorSites, RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  prove_local_path

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.constructor_shape
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.constructor_path

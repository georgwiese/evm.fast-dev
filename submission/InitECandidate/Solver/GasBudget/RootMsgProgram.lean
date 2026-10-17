import InitECandidate.Solver.GasBudget.RootTeNormal
import InitECandidate.Solver.Input.LocalPathTactics

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input

def msgGasStore : ProgHOL 64 := .store (addConst (localVar "m") 40#64) (localVar "mgas")
def msgGasSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.seq (.store (.op .add [.var .local name, .const offset]) (.var .local value)) rest) =>
      (if name = ofString "m" ∧ offset = 40#64 ∧ value = ofString "mgas" then [code] else []) ++ msgGasSites rest
  | .seq left right | .ite _ left right => msgGasSites left ++ msgGasSites right
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest => msgGasSites rest
  | _ => []
def msgGasSite : ProgHOL 64 := ((msgGasSites afterSplit)[0]?).getD .skip
def afterMsgGas : ProgHOL 64 := match msgGasSite with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 20000 in
theorem actual_msg_gas : msgGasSite = .seq msgGasStore afterMsgGas := by
  simp only [msgGasSite, afterMsgGas, afterSplit, actualSplit, validationContinuation,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, Option.map_some, continuations, RootBudget.sites, msgGasSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, msgGasStore, localVar, addConst]
  rfl

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
/-- Every instruction from the real root split to the actual MSG_GAS store,
including balance calls, TE stores, both access-list loops and optional blob/
setcode branches. This is checked local reachability, not a prefix cost. -/
theorem msg_gas_path : LocalPath "mgas" msgGasSite afterSplit := by
  simp only [msgGasSite, afterSplit, actualSplit, validationContinuation,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, Option.map_some, continuations, RootBudget.sites, msgGasSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  prove_local_path

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_msg_gas
#print axioms InitECandidate.Solver.GasBudget.RootCaller.msg_gas_path

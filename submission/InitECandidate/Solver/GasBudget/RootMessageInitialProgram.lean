import InitECandidate.Solver.GasBudget.RootMessageProgram
import InitECandidate.Solver.GasBudget.MsgNewCall

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

def recipientExpression : ExpHOL 64 := .load .one (addConst (localVar "tx") 152#64)
def beforeGas : ProgHOL 64 :=
  .seq (MessageField.store 0 (.var .global (ofString "be")))
    (.seq (MessageField.store 8 (localVar "te"))
      (.seq (MessageField.store 16 (localVar "sender"))
        (.seq (MessageField.store 24 recipientExpression) RootCaller.msgGasSite)))
def initialSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall name _ function _ rest) =>
      (if name = ofString "m" ∧ function = ofString "msg_new" then [code] else []) ++ initialSites rest
  | .seq first second | .ite _ first second => initialSites first ++ initialSites second
  | .dec _ _ _ rest | .while _ rest => initialSites rest
  | _ => []
def initialSite : ProgHOL 64 := ((initialSites RootCaller.afterSplit)[0]?).getD .skip

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem initial_shape : initialSite = .decCall (ofString "m") .one (ofString "msg_new") [] beforeGas := by
  simp only [initialSite, initialSites, beforeGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    recipientExpression, MessageField.store, addConst, localVar]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem initial_path : LocalPath "mgas" initialSite RootCaller.afterSplit := by
  simp only [initialSite, initialSites, RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  prove_local_path

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.initial_shape
#print axioms InitECandidate.Solver.GasBudget.RootMessage.initial_path

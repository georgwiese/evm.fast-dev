import InitECandidate.Solver.GasBudget.RootMessageInitialized
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def condition : ExpHOL 64 := .cmp .equal RootMessage.recipientExpression (.const 0#64)
def fields (recipient data length empty : BitVec 64) : List FieldStores.Field :=
  [⟨32, .copied 152 recipient⟩, ⟨88, .copied 192 data⟩, ⟨96, .copied 200 length⟩,
   ⟨112, .saved "empty" empty⟩, ⟨120, .literal 0#64⟩]
def lastStore : ProgHOL 64 := MessageField.store 104 RootMessage.recipientExpression
def noncreateSetup : ProgHOL 64 := FieldStores.program "m" "tx" (fields 0#64 0#64 0#64 0#64) lastStore
def afterEmpty : ProgHOL 64 := match WarmKeys.afterLoop with | .seq .skip (.decCall _ _ _ _ rest) => rest | _ => .skip
def creationSetup : ProgHOL 64 := match afterEmpty with | .seq (.ite _ yes _) _ => yes | _ => .skip
def afterChoice : ProgHOL 64 := match afterEmpty with | .seq (.ite _ _ _) rest => rest | _ => .skip
def finalSet : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set")
  [localVar "aa", .load .one (addConst (localVar "m") 32#64), .const 1#64]
def afterRecipient : ProgHOL 64 := match afterChoice with
  | .seq .skip (.seq (.store _ _) (.seq (.call _ _ _) rest)) => rest | _ => .skip
def callSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall _ _ function _ rest) =>
      (if function = ofString "process_message_call" then [code] else []) ++ callSites rest
  | .seq first second | .ite _ first second => callSites first ++ callSites second
  | .dec _ _ _ rest | .while _ rest => callSites rest
  | _ => []
def messageSite : ProgHOL 64 := ((callSites WarmKeys.afterLoop)[0]?).getD .skip

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem empty_entry : WarmKeys.afterLoop = .seq .skip (.decCall (ofString "empty") .one (ofString "alloc") [.const 8#64] afterEmpty) := by
  simp only [WarmKeys.afterLoop, WarmKeys.site, WarmKeys.sites, afterEmpty,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites, RootCaller.afterSplit,
    RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations, RootBudget.sites,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem choice_shape : afterEmpty = .seq (.ite condition creationSetup noncreateSetup) afterChoice := by
  simp only [afterEmpty, creationSetup, afterChoice, noncreateSetup, fields, lastStore, condition,
    WarmKeys.afterLoop, WarmKeys.site, WarmKeys.sites, RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations, RootBudget.sites,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, FieldStores.program, FieldStores.address, FieldStores.Value.expression,
    MessageField.store, RootMessage.recipientExpression, addConst, localVar]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem after_choice_shape : afterChoice = .seq .skip (.seq (MessageField.store 136 (.const 1#64)) (.seq finalSet afterRecipient)) := by
  simp only [afterChoice, afterRecipient, afterEmpty, WarmKeys.afterLoop, WarmKeys.site, WarmKeys.sites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites, RootCaller.afterSplit,
    RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations, RootBudget.sites,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, finalSet, MessageField.store, addConst, localVar]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem after_recipient_shape : afterRecipient = .seq .skip (.seq (MessageField.store 152 (localVar "aa")) (.seq (MessageField.store 160 (localVar "ak")) messageSite)) := by
  simp only [afterRecipient, afterChoice, afterEmpty, messageSite, callSites, WarmKeys.afterLoop, WarmKeys.site, WarmKeys.sites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites, RootCaller.afterSplit,
    RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations, RootBudget.sites,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, MessageField.store, addConst, localVar]
  rfl

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.empty_entry
#print axioms InitECandidate.Solver.GasBudget.Recipient.choice_shape
#print axioms InitECandidate.Solver.GasBudget.Recipient.after_choice_shape
#print axioms InitECandidate.Solver.GasBudget.Recipient.after_recipient_shape

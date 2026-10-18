import InitECandidate.Solver.GasBudget.RootRecipientNoncreate
import InitECandidate.Solver.GasBudget.FrameOpenNormalCall

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_process_message_call with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "msg", .one)]
def clear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "out", .const 96#64]
def afterZero : ProgHOL 64 := match body with | .seq .skip (.decCall _ _ _ _ (.seq _ rest)) => rest | _ => .skip
def afterCall : ProgHOL 64 := match Recipient.messageSite with | .decCall _ _ _ _ rest => rest | _ => .skip

theorem body_shape : body = .seq .skip (.decCall (ofString "out") .one (ofString "alloc") [.const 96#64] (.seq clear afterZero)) := by
  simp only [body, afterZero, Guest.guestFn_process_message_call, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, clear, localVar]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem actual_call : Recipient.messageSite = .decCall (ofString "out") .one (ofString "process_message_call") [localVar "m"] afterCall := by
  simp only [Recipient.messageSite, afterCall, Recipient.callSites, WarmKeys.afterLoop, WarmKeys.site, WarmKeys.sites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites, RootCaller.afterSplit,
    RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations, RootBudget.sites,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, localVar]
  rfl

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.body_shape
#print axioms InitECandidate.Solver.GasBudget.MessageCall.actual_call

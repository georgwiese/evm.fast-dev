import InitECandidate.Solver.GasBudget.RootMsgProgram
import InitECandidate.Solver.MutableTable.SetNormalCall
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def query : ExpHOL 64 := .op .add [localVar "al_keys", .panop .mul [localVar "i", .const 52#64]]
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") [localVar "ak", query, .const 1#64]
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i", .const 1#64])
def loopBody : ProgHOL 64 := .seq setCall increment
def condition : ExpHOL 64 := .cmp .less (localVar "i") (localVar "nkeys")
def loop : ProgHOL 64 := .while condition loopBody

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.seq (.while (.cmp .less (.var .local index) (.var .local count)) body) rest) =>
      (if index = ofString "i" ∧ count = ofString "nkeys" then [code] else []) ++ sites body ++ sites rest
  | .seq first second | .ite _ first second => sites first ++ sites second
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest => sites rest
  | _ => []
def site : ProgHOL 64 := ((sites RootCaller.afterMsgGas)[0]?).getD .skip
def afterLoop : ProgHOL 64 := match site with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
/-- Exact original transaction storage-key warming loop, with its real
52-byte unaligned input keys and mutation call. -/
theorem site_shape : site = .seq loop afterLoop := by
  simp only [site, afterLoop, sites, RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    loop, condition, loopBody, setCall, query, increment, localVar]
  rfl

theorem body_safe : Input.LocalPrefix (ofString "nkeys") loopBody :=
  .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ (by decide))

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.site_shape
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.body_safe

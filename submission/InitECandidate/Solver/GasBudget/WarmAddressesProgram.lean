import InitECandidate.Solver.GasBudget.WarmPrecompilesProgram

namespace InitECandidate.Solver.GasBudget.WarmAddresses
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

def total : ExpHOL 64 := .op .add [localVar "nal", .const 1#64]
def query : ExpHOL 64 := .load .one (.op .add [localVar "al_addrs", .panop .mul [localVar "i", .const 8#64]])
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") [localVar "aa", query, .const 1#64]
def increment : ProgHOL 64 := WarmKeys.increment
def loopBody : ProgHOL 64 := .seq setCall increment
def condition : ExpHOL 64 := .cmp .less (localVar "i") total
def loop : ProgHOL 64 := .while condition loopBody
def resetIndex : ProgHOL 64 := .assign .local (ofString "i") (.const 0#64)

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.seq (.while (.cmp .less (.var .local index) (.op .add [.var .local count, .const one])) body) rest) =>
      (if index = ofString "i" ∧ count = ofString "nal" ∧ one = 1#64 then [code] else []) ++ sites body ++ sites rest
  | .seq first second | .ite _ first second => sites first ++ sites second
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest => sites rest
  | _ => []
def site : ProgHOL 64 := ((sites WarmPrecompiles.afterLoop)[0]?).getD .skip
def afterLoop : ProgHOL 64 := match site with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem site_shape : site = .seq loop afterLoop := by
  simp only [site, afterLoop, sites, WarmPrecompiles.afterLoop, WarmPrecompiles.site, WarmPrecompiles.sites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    loop, condition, loopBody, setCall, query, total, increment, WarmKeys.increment, localVar]
  rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem entry_shape : WarmPrecompiles.afterLoop = .seq resetIndex site := by
  simp only [site, sites, WarmPrecompiles.afterLoop, WarmPrecompiles.site, WarmPrecompiles.sites,
    RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some, resetIndex]
  rfl

theorem body_safe : LocalPrefix (ofString "m") loopBody :=
  .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ (by decide))

end InitECandidate.Solver.GasBudget.WarmAddresses

#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.site_shape
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.entry_shape
#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.body_safe

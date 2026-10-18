import InitECandidate.Solver.GasBudget.WarmPrecompilesConstructorProgram
import InitECandidate.Solver.GasBudget.MessageFieldFrame
import InitECandidate.Solver.Input.FixedLoadShape

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def reservoirStore : ProgHOL 64 := MessageField.store 48 (localVar "reservoir")
def valueExpression : ExpHOL 64 := .load Input.fourWords (addConst (localVar "tx") 160#64)
def valueStore : ProgHOL 64 := MessageField.store 56 valueExpression

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
/-- Exactly the two original stores after MSG_GAS, followed by the checked
original account-table constructor and complete warm-up suffix. -/
theorem after_gas_shape : RootCaller.afterMsgGas = .seq reservoirStore (.seq valueStore WarmPrecompiles.constructorSite) := by
  simp only [RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    WarmPrecompiles.constructorSite, WarmPrecompiles.constructorSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    reservoirStore, valueStore, MessageField.store, valueExpression, Input.fourWords, addConst, localVar]
  rfl

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.after_gas_shape

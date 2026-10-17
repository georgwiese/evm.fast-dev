import InitECandidate.Solver.GasBudget.RootCallerNormal

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def teGasStore : ProgHOL 64 := .store (addConst (localVar "te") 80#64) (localVar "mgas")
def beforeTeGas (target : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "increment_nonce") [localVar "sender"])
    (.dec (ofString "bal") shape4 (.load shape4 (addConst (localVar "acct") 8#64))
      (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub")
          [localVar "bal", localVar "effective_gas_fee"])
        (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub")
            [localVar "bal", localVar "blob_gas_fee"])
          (.seq (.call (some (none, none)) (ofString "set_account_balance") [localVar "sender", localVar "bal"])
            (.seq .skip (.decCall (ofString "te") .one (ofString "te_new") []
              (.seq (.store (addConst (localVar "te") 0#64) (localVar "sender"))
                (.seq (.store (addConst (localVar "te") 8#64) (.load .one (addConst (localVar "tx") 152#64)))
                  (.seq (.store (addConst (localVar "te") 16#64) (.load shape4 (addConst (localVar "tx") 160#64)))
                    (.seq (.store (addConst (localVar "te") 48#64) (localVar "price")) target))))))))))

def teGasSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.seq (.store (.op .add [.var .local name, .const offset]) (.var .local value)) rest) =>
      (if name = ofString "te" ∧ offset = 80#64 ∧ value = ofString "mgas" then [code] else []) ++ teGasSites rest
  | .seq left right | .ite _ left right => teGasSites left ++ teGasSites right
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest => teGasSites rest
  | _ => []
def teGasSite : ProgHOL 64 := ((teGasSites afterSplit)[0]?).getD .skip
def afterTeGas : ProgHOL 64 := match teGasSite with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 20000 in
theorem actual_te_gas : teGasSite = .seq teGasStore afterTeGas := by
  simp only [teGasSite, afterTeGas, afterSplit, actualSplit, validationContinuation,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, Option.map_some, continuations, RootBudget.sites, teGasSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, teGasStore, localVar, addConst]
  rfl

set_option maxRecDepth 20000 in
theorem actual_before_te_gas : afterSplit = beforeTeGas teGasSite := by
  simp only [teGasSite, afterSplit, actualSplit, validationContinuation,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, Option.map_some, continuations, RootBudget.sites, teGasSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, beforeTeGas, shape4, localVar, addConst]
  rfl

/-- Actual intervening balance calls and four TE stores preserve mgas. -/
theorem te_gas_path (target : ProgHOL 64) : Input.LocalPath "mgas" target (beforeTeGas target) := by
  unfold beforeTeGas
  apply Input.LocalPath.seq
  · apply Input.LocalPrefix.call none
    intro name impossible
    cases impossible
  apply Input.LocalPath.dec _ _ _ (by decide)
  apply Input.LocalPath.seq
  · apply Input.LocalPrefix.call (some (ofString "bal"))
    intro name same
    cases same
    decide
  apply Input.LocalPath.seq
  · apply Input.LocalPrefix.call (some (ofString "bal"))
    intro name same
    cases same
    decide
  apply Input.LocalPath.seq
  · apply Input.LocalPrefix.call none
    intro name impossible
    cases impossible
  apply Input.LocalPath.seq _ .skip
  apply Input.LocalPath.decCall _ _ _ _ (by decide)
  apply Input.LocalPath.seq _ (.store _ _)
  apply Input.LocalPath.seq _ (.store _ _)
  apply Input.LocalPath.seq _ (.store _ _)
  apply Input.LocalPath.seq _ (.store _ _)
  exact .here

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_te_gas
#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_before_te_gas
#print axioms InitECandidate.Solver.GasBudget.RootCaller.te_gas_path

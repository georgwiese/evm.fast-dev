import InitECandidate.Solver.GasBudget.RootEntry
import InitECandidate.Solver.Input.LocalPath

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def shape4 : ShapeHOL := .comb [.one, .one, .one, .one]
def shape5 : ShapeHOL := .comb [.one, .one, .one, .one, .one]
def blobBranch : ProgHOL 64 :=
  .ite (.cmp .notEqual (localVar "tx_blob_gas_used") (.const 0#64))
    (.decCall (ofString "bgp") shape4 (ofString "calculate_blob_gas_price")
      [.load .one (addConst (.var .global (ofString "be")) 96#64)]
      (.decCall (ofString "bgf") shape5 (ofString "fee_mul") [localVar "tx_blob_gas_used", localVar "bgp"]
        (.assign .local (ofString "blob_gas_fee") (.rstruct [
          .rfield 1 (localVar "bgf"), .rfield 2 (localVar "bgf"),
          .rfield 3 (localVar "bgf"), .rfield 4 (localVar "bgf")])))) .skip

def beforeSplit (target : ProgHOL 64) : ProgHOL 64 :=
  .seq .skip
    (.dec (ofString "intrinsic_gas") .one (.op .add [.rfield 0 (localVar "intrinsic"), .rfield 1 (localVar "intrinsic")])
      (.decCall (ofString "price") shape4 (ofString "check_transaction") [localVar "tx", localVar "sender"]
        (.seq .skip
          (.decCall (ofString "tx_blob_gas_used") .one (ofString "calculate_total_blob_gas") [localVar "tx"]
            (.decCall (ofString "acct") .one (ofString "get_account") [localVar "sender"]
              (.seq .skip
                (.dec (ofString "blob_gas_fee") shape4 (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])
                  (.seq blobBranch
                    (.dec (ofString "gas") .one (.load .one (addConst (localVar "tx") 144#64))
                      (.decCall (ofString "egf") shape5 (ofString "fee_mul") [localVar "gas", localVar "price"]
                        (.dec (ofString "effective_gas_fee") shape4 (.rstruct [
                          .rfield 1 (localVar "egf"), .rfield 2 (localVar "egf"),
                          .rfield 3 (localVar "egf"), .rfield 4 (localVar "egf")]) target)))))))))))

def continuations : ProgHOL 64 → List (ProgHOL 64)
  | .decCall name _ _ _ rest =>
      (if name = ofString "intrinsic" then [rest] else []) ++ continuations rest
  | .seq first second | .ite _ first second => continuations first ++ continuations second
  | .dec _ _ _ rest | .while _ rest => continuations rest
  | _ => []
def validationContinuation : ProgHOL 64 := match Guest.guestFn_process_transaction with
  | .function fn => ((continuations (progToHOL fn.body))[0]?).getD .skip
  | _ => .skip
def actualSplit : ProgHOL 64 := ((RootBudget.sites validationContinuation)[0]?).getD .skip

def afterSplit : ProgHOL 64 := match actualSplit with
  | .dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.dec _ _ _ rest))) => rest
  | _ => .skip

set_option maxRecDepth 10000 in
theorem actual_split : actualSplit = RootBudget.program afterSplit := by
  simp only [afterSplit, actualSplit, validationContinuation, Guest.guestFn_process_transaction,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    continuations, RootBudget.sites, ↓reduceIte, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, Option.getD_some, RootBudget.program,
    RootBudget.executionExpression, RootBudget.regularExpression, RootBudget.minArguments,
    RootBudget.reservoirExpression, localVar]
  rfl

set_option maxRecDepth 10000 in
/-- The exact original caller between validation and the root gas split. -/
theorem actual_prefix : validationContinuation = beforeSplit actualSplit := by
  simp only [validationContinuation, actualSplit, Guest.guestFn_process_transaction, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some, continuations, RootBudget.sites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, beforeSplit, blobBranch, shape4, shape5, localVar, addConst]
  rfl

/-- The conditional blob-fee helpers may change memory, but they cannot
return from the caller or alter its saved intrinsic binding. -/
theorem blob_local : Input.LocalPrefix (ofString "intrinsic") blobBranch := by
  unfold blobBranch
  apply Input.LocalPrefix.ite
  · apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    exact Input.LocalPrefix.assign _ _ (by decide)
  · exact .skip

theorem prefix_path (target : ProgHOL 64) : Input.LocalPath "intrinsic" target (beforeSplit target) := by
  unfold beforeSplit
  apply Input.LocalPath.seq _ .skip
  apply Input.LocalPath.dec _ _ _ (by decide)
  apply Input.LocalPath.decCall _ _ _ _ (by decide)
  apply Input.LocalPath.seq _ .skip
  apply Input.LocalPath.decCall _ _ _ _ (by decide)
  apply Input.LocalPath.decCall _ _ _ _ (by decide)
  apply Input.LocalPath.seq _ .skip
  apply Input.LocalPath.dec _ _ _ (by decide)
  apply Input.LocalPath.seq _ blob_local
  apply Input.LocalPath.dec _ _ _ (by decide)
  apply Input.LocalPath.decCall _ _ _ _ (by decide)
  apply Input.LocalPath.dec _ _ _ (by decide)
  exact .here

/-- The complete real normal prefix reaches the actual split with the
validator's caps intact. No intermediate helper or read premise remains. -/
theorem normal_reaches (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (capped : RootValidation.CappedIntrinsic source)
    (run : evaluateHOLFiniteState source validationContinuation = (some (.returned value), post)) :
    ∃ ready finish : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState ready actualSplit = (some (.returned value), finish) ∧
      RootValidation.CappedIntrinsic ready ∧ ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  rw [actual_prefix] at run
  obtain ⟨ready, finish, suffixRun, localEq, codes, shapes⟩ :=
    (prefix_path actualSplit).normal_reaches source post value run
  obtain ⟨regular, state, floor, stored, regularCap, floorCap⟩ := capped
  exact ⟨ready, finish, suffixRun, ⟨regular, state, floor, localEq.trans stored, regularCap, floorCap⟩, codes, shapes⟩

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_prefix
#print axioms InitECandidate.Solver.GasBudget.RootCaller.prefix_path
#print axioms InitECandidate.Solver.GasBudget.RootCaller.normal_reaches

#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_split

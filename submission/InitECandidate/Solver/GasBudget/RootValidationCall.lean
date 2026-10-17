import InitECandidate.Solver.GasBudget.RootValidatedResult
import InitECandidate.Solver.Input.NormalCallData

namespace InitECandidate.Solver.GasBudget.RootValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def validationFormals : List (MlS × ShapeHOL) := [(ofString "tx", .one), (ofString "sender", .one)]
def CappedIntrinsic (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ regular state floor : BitVec 64,
    source.locals.lookup (ofString "intrinsic") = some (RootBudget.intrinsicValue regular state floor) ∧
    regular.toNat ≤ 16777216 ∧ floor.toNat ≤ 16777216

def callSites : ProgHOL 64 → List (ProgHOL 64)
  | .decCall name shape function arguments rest =>
      (if function = ofString "validate_transaction" then
        [.decCall name shape function arguments .skip] else []) ++ callSites rest
  | .seq left right | .ite _ left right => callSites left ++ callSites right
  | .dec _ _ _ rest | .while _ rest => callSites rest
  | _ => []
def selectedCalls : List (ProgHOL 64) := match Guest.guestFn_process_transaction with
  | .function fn => callSites (progToHOL fn.body)
  | _ => []

set_option maxRecDepth 10000 in
theorem actual_call_site : selectedCalls =
    [.decCall (ofString "intrinsic") intrinsicShape (ofString "validate_transaction")
      [localVar "tx", localVar "sender"] .skip] := by
  simp only [selectedCalls, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, callSites, ↓reduceIte,
    List.nil_append, List.cons_append, List.append_nil, intrinsicShape, localVar]
  rfl

private theorem looked_body
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (parameters : List (MlS × ShapeHOL)) (knownBody : ProgHOL 64) (knownShape : ShapeHOL)
    (values : List (ValueHOL 64)) (actualBody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (stored : code function = some (parameters, knownBody, knownShape))
    (called : lookupCodeHOLFinite code function values = some (actualBody, callee, returnShape)) : actualBody = knownBody := by
  have raw := lookupCodeHOLFinite_eq_some code function values actualBody callee returnShape called
  simp only [lookupCodeHOLExact, stored] at raw
  split at raw
  · have equal := Option.some.inj raw
    exact (congrArg Prod.fst equal).symm
  · cases raw

/-- A real normal validate_transaction call derives the caller's intrinsic
triple/caps and continuation run, rather than assuming its callee result. -/
theorem normal_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (code : source.code.lookup (ofString "validate_transaction") = some (validationFormals, body, intrinsicShape))
    (shape : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source
      (.decCall (ofString "intrinsic") intrinsicShape (ofString "validate_transaction") arguments continuation) =
        (some (.returned returned), post)) :
    ∃ calleePost intrinsic inner,
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost "intrinsic" intrinsic) continuation =
        (some (.returned returned), inner) ∧
      post = restore source "intrinsic" inner ∧
      CappedIntrinsic (Input.CallNormal.continuationEntry source calleePost "intrinsic" intrinsic) ∧
      calleePost.eshapes = source.eshapes ∧ calleePost.code = source.code := by
  obtain ⟨values, calleeBody, callee, returnShape, calleePost, intrinsic, inner,
    args, called, bodyRun, continuationRun, restored, domain, endian, shapes, codes, typed⟩ :=
    Input.CallNormal.normal_data source post "intrinsic" intrinsicShape (ofString "validate_transaction") arguments continuation returned run
  have bodyEq := looked_body source.code.lookup (ofString "validate_transaction") validationFormals body intrinsicShape
    values calleeBody callee returnShape code called
  rw [bodyEq] at bodyRun
  obtain ⟨regular, state, floor, intrinsicEq, regularCap, floorCap⟩ :=
    normal_result (callEntryStateHOLFinite source callee) calleePost intrinsic shape bodyRun
  refine ⟨calleePost, intrinsic, inner, continuationRun, restored, ?_, shapes, codes⟩
  refine ⟨regular, state, floor, ?_, regularCap, floorCap⟩
  simp [Input.CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, intrinsicEq]

end InitECandidate.Solver.GasBudget.RootValidation

#print axioms InitECandidate.Solver.GasBudget.RootValidation.normal_call

#print axioms InitECandidate.Solver.GasBudget.RootValidation.actual_call_site

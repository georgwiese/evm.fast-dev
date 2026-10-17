import InitECandidate.Solver.GasBudget.RootCallerProgram
import InitECandidate.Solver.GasBudget.RootNormalEntry

namespace InitECandidate.Solver.GasBudget.RootCaller
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def validationCall : ProgHOL 64 :=
  .decCall (ofString "intrinsic") RootValidation.intrinsicShape (ofString "validate_transaction")
    [localVar "tx", localVar "sender"] validationContinuation

def fullValidationSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall _ _ function _ rest) =>
      (if function = ofString "validate_transaction" then [code] else []) ++ fullValidationSites rest
  | .seq left right | .ite _ left right => fullValidationSites left ++ fullValidationSites right
  | .dec _ _ _ rest | .while _ rest => fullValidationSites rest
  | _ => []
def selectedValidationSites : List (ProgHOL 64) := match Guest.guestFn_process_transaction with
  | .function fn => fullValidationSites (progToHOL fn.body)
  | _ => []

set_option maxRecDepth 10000 in
/-- The full original call, including its real unmodified continuation. -/
theorem actual_validation_call : selectedValidationSites = [validationCall] := by
  simp only [selectedValidationSites, validationCall, validationContinuation,
    Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, Option.map_some, fullValidationSites, continuations,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, RootValidation.intrinsicShape, localVar]
  rfl

/-- From a real normal execution of the validator call through its complete
caller suffix, derive the actual root gas initialization and cap. No intrinsic
value, intermediate helper success, gas read or clock availability is assumed.
This theorem does not yet bound the caller's preprocessing runtime or connect
the words to TE/MSG/frame memory. -/
theorem normal_root (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (validator : source.code.lookup (ofString "validate_transaction") =
      some (RootValidation.validationFormals, RootValidation.body, RootValidation.intrinsicShape))
    (minimum : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (txError : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source validationCall = (some (.returned value), post)) :
    ∃ (splitSource finish : PanSemStateFiniteExact 64 Guest.HostMemory) (gas intrinsic regular state floor : BitVec 64),
      evaluateHOLFiniteState (RootBudget.entered splitSource gas intrinsic regular) afterSplit =
        (some (.returned value), finish) ∧
      (RootBudget.liquidWord gas intrinsic regular).toNat + regular.toNat ≤ 16777216 ∧
      floor.toNat ≤ 16777216 ∧
      (RootBudget.entered splitSource gas intrinsic regular).locals.lookup (ofString "mgas") =
        some (.val (.word (RootBudget.liquidWord gas intrinsic regular))) ∧
      (RootBudget.entered splitSource gas intrinsic regular).locals.lookup (ofString "reservoir") =
        some (.val (.word (RootBudget.reservoirWord gas intrinsic regular))) ∧
      splitSource.locals.lookup (ofString "intrinsic") = some (RootBudget.intrinsicValue regular state floor) ∧
      splitSource.code = source.code ∧ splitSource.eshapes = source.eshapes := by
  obtain ⟨calleePost, intrinsicValue, inner, tailRun, restored, capped, calleeShapes, calleeCodes⟩ :=
    RootValidation.normal_call source post [localVar "tx", localVar "sender"] validationContinuation value
      validator txError run
  obtain ⟨splitSource, splitPost, splitRun, splitCapped, splitCodes, splitShapes⟩ :=
    normal_reaches _ inner value capped tailRun
  have codes : splitSource.code = source.code := splitCodes.trans calleeCodes
  have shapes : splitSource.eshapes = source.eshapes := splitShapes.trans calleeShapes
  have minCode : splitSource.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one) := by
    rw [codes]
    exact minimum
  rw [actual_split] at splitRun
  obtain ⟨gas, intrinsic, regular, state, floor, finish, suffixRun, liquidCap, floorCap,
    stored, gasLocal, totalLocal, enough⟩ :=
    RootBudget.normal_initialize splitSource splitPost afterSplit value splitCapped minCode splitRun
  have fields := RootBudget.entered_fields splitSource gas intrinsic regular
  exact ⟨splitSource, finish, gas, intrinsic, regular, state, floor, suffixRun, liquidCap,
    floorCap, fields.2.2.2.2.1, fields.2.2.2.2.2, stored, codes, shapes⟩

end InitECandidate.Solver.GasBudget.RootCaller

#print axioms InitECandidate.Solver.GasBudget.RootCaller.actual_validation_call
#print axioms InitECandidate.Solver.GasBudget.RootCaller.normal_root

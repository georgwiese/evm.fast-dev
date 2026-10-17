import InitECandidate.Solver.GasBudget.RootValidationProgram
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.RootValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

 def fieldValue (value : ValueHOL 64) (index : Nat) : Option (ValueHOL 64) :=
  match value with
  | .rStruct fields => fields[index]?
  | _ => none

private theorem local_other (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name other : String) (value : ValueHOL 64) (different : ofString name ≠ ofString other) :
    (setVarHOLFinite (ofString name) value source).locals.lookup (ofString other) =
      source.locals.lookup (ofString other) := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]

theorem field_of_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (index : Nat)
    (stored : source.locals.lookup (ofString "ic") = some value) :
    eval source (field index) = fieldValue value index := by
  cases value <;> simp [eval, field, fieldValue, localVar, evalHOLExact, toExact, stored]

/-- Later nonce declarations, helper calls and validation guards cannot replace
an intrinsic value returned by the earlier calculation. -/
theorem nonce_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (intrinsic returned : ValueHOL 64)
    (stored : source.locals.lookup (ofString "ic") = some intrinsic)
    (run : evaluateHOLFiniteState source nonceBody = (some (.returned returned), post)) : returned = intrinsic := by
  rw [nonceBody] at run
  obtain ⟨nonce, noncePost, nonceRead, nonceShapePass, nonceRun, nonceRestore⟩ :=
    Input.CallNormal.declaration_normal_entry source post "nonce" nonceShape nonceExpression _ returned run
  let afterNonce := setVarHOLFinite (ofString "nonce") nonce source
  have icNonce : afterNonce.locals.lookup (ofString "ic") = some intrinsic :=
    (local_other source "nonce" "ic" nonce (by decide)).trans stored
  obtain ⟨fitsPost, fitsValue, inner, fitsRun, fitsRestore, domain, endian, shapes, codes, shapePass⟩ :=
    Input.CallNormal.normal_entry afterNonce noncePost "fits" .one (ofString "u256_fits_word")
      [localVar "nonce"] fitsBody returned nonceRun
  let ready := Input.CallNormal.continuationEntry afterNonce fitsPost "fits" fitsValue
  have icReady : ready.locals.lookup (ofString "ic") = some intrinsic :=
    (local_other { fitsPost with locals := afterNonce.locals } "fits" "ic" fitsValue (by decide)).trans icNonce
  change evaluateHOLFiniteState ready fitsBody = _ at fitsRun
  rw [fitsBody] at fitsRun
  have later := nonce_guards_pure.1.normal_continue ready inner (.seq nonceGuard (.return (localVar "ic"))) returned fitsRun
  have last := nonce_guards_pure.2.normal_continue ready inner (.return (localVar "ic")) returned later
  have read : eval ready (localVar "ic") = some intrinsic := by
    simp [eval, localVar, evalHOLExact, toExact, icReady]
  simp only [eval] at read
  rw [evaluateHOLFiniteState_return, read] at last
  simp only at last
  split at last
  · have equal := congrArg Prod.fst last
    cases equal
    rfl
  · cases last

/-- Every normal return of the complete unchanged validate_transaction derives
both intrinsic caps. No transaction validity, helper success, intrinsic word
reads, gas amount, memory ownership or clock allowance is assumed. -/
theorem normal_caps (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (shape : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ regular floor : BitVec 64,
      fieldValue returned 0 = some (.val (.word regular)) ∧
      fieldValue returned 2 = some (.val (.word floor)) ∧
      regular.toNat ≤ 16777216 ∧ floor.toNat ≤ 16777216 ∧
      shapeEqHOL (shapeOfHOLExact returned) intrinsicShape = true := by
  rw [body_shape] at run
  obtain ⟨intrinsicPost, intrinsic, afterIntrinsicPost, intrinsicRun, intrinsicRestore,
    domain, endian, shapes, codes, shapePass⟩ :=
    Input.CallNormal.normal_entry source post "ic" intrinsicShape (ofString "calculate_intrinsic_cost")
      [localVar "tx", localVar "sender"] intrinsicBody returned run
  let icState := Input.CallNormal.continuationEntry source intrinsicPost "ic" intrinsic
  have icLocal : icState.locals.lookup (ofString "ic") = some intrinsic := by
    simp [icState, Input.CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have icShape : icState.eshapes.lookup (ofString "TxErr") = some .one := by
    change intrinsicPost.eshapes.lookup (ofString "TxErr") = _
    rw [shapes]
    exact shape
  change evaluateHOLFiniteState icState intrinsicBody = _ at intrinsicRun
  rw [intrinsicBody] at intrinsicRun
  obtain ⟨gas, gasPost, gasRead, gasShape, gasRun, gasRestore⟩ :=
    Input.CallNormal.declaration_normal_entry icState afterIntrinsicPost "gas" .one gasExpression gasBody returned intrinsicRun
  let ready := setVarHOLFinite (ofString "gas") gas icState
  have icReady : ready.locals.lookup (ofString "ic") = some intrinsic :=
    (local_other icState "gas" "ic" gas (by decide)).trans icLocal
  have readyShape : ready.eshapes.lookup (ofString "TxErr") = some .one := icShape
  change evaluateHOLFiniteState ready gasBody = _ at gasRun
  rw [gasBody] at gasRun
  have p0 := prefix_guards_pure.1.normal_continue ready gasPost
    (.seq totalGuard (.seq floorGasGuard (.seq codeGuard capBody))) returned gasRun
  have p1 := prefix_guards_pure.2.1.normal_continue ready gasPost
    (.seq floorGasGuard (.seq codeGuard capBody)) returned p0
  have p2 := prefix_guards_pure.2.2.1.normal_continue ready gasPost (.seq codeGuard capBody) returned p1
  have capRun := prefix_guards_pure.2.2.2.normal_continue ready gasPost capBody returned p2
  rw [capBody] at capRun
  obtain ⟨regular, regularRead, regularCap⟩ := normal_field ready gasPost 0 63#64
    (.seq (guard 2 64#64) nonceBody) returned readyShape capRun
  have floorRun := (cap_guard_pure 0 63#64).normal_continue ready gasPost
    (.seq (guard 2 64#64) nonceBody) returned capRun
  obtain ⟨floor, floorRead, floorCap⟩ := normal_field ready gasPost 2 64#64 nonceBody returned readyShape floorRun
  have nonceRun := (cap_guard_pure 2 64#64).normal_continue ready gasPost nonceBody returned floorRun
  have returnedEq := nonce_normal_value ready gasPost intrinsic returned icReady nonceRun
  refine ⟨regular, floor, ?_, ?_, regularCap, floorCap, ?_⟩
  · rw [returnedEq]
    exact (field_of_local ready intrinsic 0 icReady).symm.trans regularRead
  · rw [returnedEq]
    exact (field_of_local ready intrinsic 2 icReady).symm.trans floorRead

  · simpa only [returnedEq] using shapePass

end InitECandidate.Solver.GasBudget.RootValidation

#print axioms InitECandidate.Solver.GasBudget.RootValidation.field_of_local
#print axioms InitECandidate.Solver.GasBudget.RootValidation.nonce_normal_value
#print axioms InitECandidate.Solver.GasBudget.RootValidation.normal_caps

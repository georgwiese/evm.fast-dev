import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The mask aligns the actual word even when the preceding addition wraps.
Natural room/monotonicity is deliberately not asserted by this lemma. -/
theorem rounded_aligned_word (pointer amount : BitVec 64) :
    (rounded pointer amount).toNat % 8 = 0 := by
  rw [rounded, BitVec.toNat_and]
  change ((pointer + amount + 7#64).toNat &&& (0#64 - 8#64).toNat) % 2^3 = 0
  rw [Nat.and_mod_two_pow]
  change ((pointer + amount + 7#64).toNat % 8) &&& 0 = 0
  exact Nat.and_zero _

/-- Derive both actual guard tests and the real checked post-state from an
observed allocator return. No initial heap-end or no-wrap premise is needed.
The bounded aligned cursor comes from the second guard and literal bit mask. -/
theorem checked_post_of_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    value = .val (.word pointer) ∧
      (rounded pointer amount).toNat ≤ 2952790016 ∧
      (rounded pointer amount).toNat % 8 = 0 ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (post source pointer amount) := by
  classical
  let entered := bind source "p" pointer
  have pointerRead : eval source heapVar = some (.val (.word pointer)) := by
    simp [eval, heapVar, evalHOLExact, toExact, heapGlobal]
  have full := normal
  rw [body_shape] at full
  obtain ⟨inner, tailRun, restored⟩ := Input.declaration_return_word source target "p" heapVar pointer pTail value pointerRead full
  have pLocal : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : entered.locals.lookup (ofString "n") = some (.val (.word amount)) :=
    (bind_lookup_other source "p" "n" _ (by decide)).trans amountLocal
  have safe : Input.LocalPrefix (ofString "n") firstGuard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle, firstRun, remaining, saved⟩ := safe.normal_continue entered inner
    (.dec (ofString "q") .one roundExpression qTail) value tailRun
  have fit : ¬ heapEnd - pointer < amount := by
    intro bad
    have chosen : evaluateHOLFiniteState entered firstGuard = evaluateHOLFiniteState entered trap := by
      rw [firstGuard, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, valueIsWord, valueWord,
        wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [.const 1#64] = some (Input.Trap.values 1#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Input.Trap.values]
    exact Input.Trap.call_not_normal entered middle [.const 1#64] 1#64 trapCode args (chosen.symm.trans firstRun)
  have firstSkip : evaluateHOLFiniteState entered firstGuard = (none, entered) := by
    rw [firstGuard, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, valueIsWord, valueWord,
      wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, fit]
  have same : middle = entered := (congrArg Prod.snd (firstRun.symm.trans firstSkip))
  rw [same] at remaining
  have qRead : eval entered roundExpression = some (.val (.word (rounded pointer amount))) := by
    simp [eval, roundExpression, rounded, localVar, evalHOLExact, evalListHOLExact, toExact,
      pLocal, nLocal, valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, BitVec.add_assoc]
  obtain ⟨qPost, qRun, qRestored⟩ := Input.declaration_return_word entered inner "q" roundExpression
    (rounded pointer amount) qTail value qRead remaining
  let qState := bind entered "q" (rounded pointer amount)
  have qLocal : qState.locals.lookup (ofString "q") = some (.val (.word (rounded pointer amount))) := bind_lookup_same _ _ _
  have qSafe : Input.LocalPrefix (ofString "q") secondGuard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨guarded, secondRun, afterGuard, savedQ⟩ := qSafe.normal_continue qState qPost
    (.seq assignment returnPointer) value qRun
  have roundedFit : ¬ heapEnd < rounded pointer amount := by
    intro bad
    have chosen : evaluateHOLFiniteState qState secondGuard = evaluateHOLFiniteState qState trap := by
      rw [secondGuard, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, toExact, localVar, qLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    have args : evalListHOLFinite qState (h := fun address => Classical.propDecidable (qState.memaddrs address)) [.const 1#64] = some (Input.Trap.values 1#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Input.Trap.values]
    exact Input.Trap.call_not_normal qState guarded [.const 1#64] 1#64 trapCode args (chosen.symm.trans secondRun)
  obtain ⟨expected, actual, frame⟩ := execute source pointer amount amountLocal heapGlobal fit roundedFit
  have equal := normal.symm.trans actual
  have valueEq : value = .val (.word pointer) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst equal
  have stateEq : target = expected := congrArg Prod.snd equal
  refine ⟨valueEq, ?_, rounded_aligned_word pointer amount, ?_⟩
  · change ¬ 2952790016 < (rounded pointer amount).toNat at roundedFit
    omega
  · rw [stateEq]; exact frame

/-- An actually returning allocator reads a scalar heap cell and leaves a
bounded aligned scalar heap cell. Neither cell nor initial heap bound is
assumed here; only the real scalar request and installed trap are supplied. -/
theorem reached_cursor (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    ∃ pointer, value = .val (.word pointer) ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (rounded pointer amount))) ∧
      (rounded pointer amount).toNat ≤ 2952790016 ∧ (rounded pointer amount).toNat % 8 = 0 := by
  have full := normal
  rw [body_shape] at full
  obtain ⟨declared, inner, read, checked, actual, restored⟩ :=
    Input.CallNormal.declaration_normal_entry source target "p" .one heapVar pTail value full
  have scalar := (shapeEqHOL_eq_true _ _).mp checked
  have declaredScalar : ∃ pointer : BitVec 64, declared = .val (.word pointer) := by
    cases declared with
    | val payload => cases payload with | word pointer => exact ⟨pointer, rfl⟩
    | rStruct fields => simp only [shapeOfHOLExact] at scalar; cases scalar
    | nStruct name fields => simp only [shapeOfHOLExact] at scalar; cases scalar
  obtain ⟨pointer, rfl⟩ := declaredScalar
  have heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := read
  obtain ⟨valueEq, bound, aligned, frame⟩ := checked_post_of_normal source target pointer amount amountLocal heapGlobal trapCode value normal
  have heapEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup (ofString "heap_ptr")) frame
  refine ⟨pointer, valueEq, ?_, bound, aligned⟩
  exact heapEq.trans (by simp [emptyLocalsHOLFinite, post, HolFiniteMapExact.update, FUPDATE])

/-- For a real nonwrapping request, the observed second allocator guard
supplies natural persistent room. No initial persistent heap bound is needed;
the caller derives no-wrap from its earlier arena and bounded request. -/
theorem post_of_normal_no_wrap (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n")=some (.val (.word amount)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (noWrap : pointer.toNat+amount.toNat+7<2^64)
    (trapCode : source.code.lookup (ofString "trap_with")=some (Input.Trap.formals,Input.Trap.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word pointer) ∧ pointer.toNat+amount.toNat≤2952790016 ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite (post source pointer amount) := by
  obtain ⟨answer,bounded,aligned,frame⟩:=checked_post_of_normal source target pointer amount amountLocal heapGlobal trapCode value normal
  have number:=rounded_nat pointer amount noWrap
  have grows : pointer.toNat+amount.toNat≤(rounded pointer amount).toNat:=by rw [number]; omega
  exact ⟨answer,by omega,frame⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.rounded_aligned_word
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.checked_post_of_normal
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.reached_cursor

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.post_of_normal_no_wrap

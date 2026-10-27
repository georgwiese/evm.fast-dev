import InitECandidate.Solver.WitnessRadix.AllocationChecked

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A returning allocator must have read a scalar request in its real first
guard. This is derived from the observed execution, not a callee-entry premise. -/
theorem request_of_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    ∃ amount : BitVec 64, source.locals.lookup (ofString "n") = some (.val (.word amount)) := by
  let entered := bind source "p" pointer
  have read : eval source heapVar = some (.val (.word pointer)) := by
    simp [eval, heapVar, evalHOLExact, toExact, heap]
  rw [body_shape] at actual
  obtain ⟨inner, tailRun, restored⟩ := Input.declaration_return_word source target "p" heapVar pointer pTail value read actual
  have safe : Input.LocalPrefix (ofString "n") firstGuard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle, guardRun, remaining, saved⟩ := safe.normal_continue entered inner
    (.dec (ofString "q") .one roundExpression qTail) value tailRun
  have pCell : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nCell : entered.locals.lookup (ofString "n") = source.locals.lookup (ofString "n") := bind_lookup_other _ "p" "n" _ (by decide)
  cases request : source.locals.lookup (ofString "n") with
  | none =>
    simp [firstGuard, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, toExact,
      localVar, pCell, nCell, request, valueIsWord, valueWord, wordOpHOL, wordOp] at guardRun
  | some data =>
    cases data with
    | val payload => cases payload with | word amount => exact ⟨amount, rfl⟩
    | rStruct fields =>
      simp [firstGuard, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, toExact,
        localVar, pCell, nCell, request, valueIsWord, valueWord, wordOpHOL, wordOp] at guardRun
    | nStruct name fields =>
      simp [firstGuard, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, toExact,
        localVar, pCell, nCell, request, valueIsWord, valueWord, wordOpHOL, wordOp] at guardRun

/-- A real allocator return from a bounded current heap cursor moves the
cursor forward and retains the bound/alignment. Request type and room are
derived from actual execution, including all malformed request cases. -/
theorem monotone_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 2952790016)
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    ∃ next : BitVec 64, target.globals.lookup (ofString "heap_ptr") = some (.val (.word next)) ∧
      pointer.toNat ≤ next.toNat ∧ next.toNat ≤ 2952790016 ∧ next.toNat % 8 = 0 := by
  obtain ⟨amount, request⟩ := request_of_return source target pointer heap value actual
  obtain ⟨returned, room, frame⟩ := post_of_normal source target pointer amount request heap bounded trapCode value actual
  have guards := guards pointer amount room
  have current := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup (ofString "heap_ptr")) frame
  refine ⟨rounded pointer amount, ?_, by have := guards.2.2.1; omega, guards.2.2.2.1, guards.2.2.2.2⟩
  exact current.trans (by simp [emptyLocalsHOLFinite, post, HolFiniteMapExact.update, FUPDATE])

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.request_of_return
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.monotone_return

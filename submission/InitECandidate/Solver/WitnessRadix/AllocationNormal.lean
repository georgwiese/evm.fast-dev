import InitECandidate.Solver.WitnessRadix.AllocationArithmetic
import InitECandidate.Solver.Input.TrapNoReturn
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real normal original allocator return derives natural request room.
The only initial cursor premise is its existing heap-end invariant. The
actual fixed trap routine is proved unable to continue normally. -/
theorem room_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (pointer amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    pointer.toNat + amount.toNat ≤ 33806089496 := by
  classical
  let entered := WitnessRadix.QueryBranch.bind source "p" pointer
  have pointerRead : eval source heapVar = some (.val (.word pointer)) := by
    simp [eval, heapVar, evalHOLExact, toExact, heapGlobal]
  have setup : BuildEntry.Initializes source [("p", heapVar)] entered (fun output => restore source "p" output) :=
    .step pointer pointerRead (.done _)
  have declared := BuildEntry.declarations_execute setup pTail
  have declaredNormal := normal
  rw [body_shape] at declaredNormal
  have resultEq := congrArg Prod.fst (declared.symm.trans declaredNormal)
  change (evaluateHOLFiniteState entered pTail).1 = some (.returned value) at resultEq
  have tailRun : evaluateHOLFiniteState entered pTail = (some (.returned value), (evaluateHOLFiniteState entered pTail).2) := Prod.ext resultEq rfl
  have safe : Input.LocalPrefix (ofString "n") firstGuard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle, firstRun, _, _⟩ := safe.normal_continue entered (evaluateHOLFiniteState entered pTail).2
    (.dec (ofString "q") .one roundExpression qTail) value tailRun
  have pLocal : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : entered.locals.lookup (ofString "n") = some (.val (.word amount)) :=
    (bind_lookup_other _ "p" "n" _ (by decide)).trans amountLocal
  have fit : ¬ heapEnd - pointer < amount := by
    intro bad
    have chosen : evaluateHOLFiniteState entered firstGuard = evaluateHOLFiniteState entered trap := by
      rw [firstGuard, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, valueIsWord, valueWord,
        wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    have trapRun := chosen.symm.trans firstRun
    have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [.const 1#64] = some (Input.Trap.values 1#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Input.Trap.values]
    exact Input.Trap.call_not_normal entered middle [.const 1#64] 1#64 trapCode args trapRun
  have pointerLe : pointer ≤ heapEnd := pointerBound
  have difference := BitVec.toNat_sub_of_le pointerLe
  change (heapEnd - pointer).toNat = 33806089496 - pointer.toNat at difference
  change ¬ (heapEnd - pointer).toNat < amount.toNat at fit
  rw [difference] at fit
  omega

/-- The actual normal allocator result and its exact nonlocal state follow
from the derived request room, rather than an assumed allocator outcome. -/
theorem post_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (pointer amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    value = .val (.word pointer) ∧ pointer.toNat + amount.toNat ≤ 33806089496 ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (post source pointer amount) := by
  have room := room_of_normal source target pointer amount amountLocal heapGlobal pointerBound trapCode value normal
  have checked := guards pointer amount room
  obtain ⟨expected, actual, frame⟩ := execute source pointer amount amountLocal heapGlobal checked.1 checked.2.1
  have same := normal.symm.trans actual
  have resultEq := congrArg Prod.fst same
  have targetEq := congrArg Prod.snd same
  refine ⟨?_, room, ?_⟩
  · simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  · change target = expected at targetEq
    rw [targetEq]
    exact frame

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.room_of_normal
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.post_of_normal

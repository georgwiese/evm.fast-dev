import InitECandidate.Solver.WitnessRadix.TableHeader
import InitECandidate.Solver.WitnessRadix.AllocationExpected
import InitECandidate.Solver.WitnessRadix.AllocatedLayout

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def initialActions : List Action := [.allocate "t" (.const 72#64), .declare "stride" stride] ++ headerActions
def initialState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  headerState (bind (PersistentAlloc.nextState source "t" plan.table (plan.table + 72)) "stride" 32#64)
    (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 plan.capacity)

/-- Actual table allocation, stride declaration and first four header stores,
from natural allocated-layout and source ABI/domain/code facts. -/
theorem initial_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (enough : 1 ≤ source.clock) :
    ∃ restoreStack, Executes source initialActions (initialState source plan) restoreStack := by
  let allocated := PersistentAlloc.nextState source "t" plan.table (plan.table + 72)
  let entered := bind allocated "stride" 32#64
  have allocatedKey : allocated.locals.lookup (ofString "key_len") = some (.val (.word 32#64)) := by
    unfold allocated PersistentAlloc.nextState
    rw [bind_lookup_other _ "t" "key_len" _ (by decide)]
    exact keyLocal
  have allocatedCap : allocated.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))) := by
    unfold allocated PersistentAlloc.nextState
    rw [bind_lookup_other _ "t" "cap" _ (by decide)]
    exact capLocal
  have enteredKey : entered.locals.lookup (ofString "key_len") = some (.val (.word 32#64)) :=
    (bind_lookup_other allocated "stride" "key_len" _ (by decide)).trans allocatedKey
  have enteredCap : entered.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))) :=
    (bind_lookup_other allocated "stride" "cap" _ (by decide)).trans allocatedCap
  have enteredTable : entered.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 plan.table))) := by
    rw [bind_lookup_other allocated "stride" "t" _ (by decide)]
    exact bind_lookup_same _ _ _
  have enteredStride : entered.locals.lookup (ofString "stride") = some (.val (.word 32#64)) := bind_lookup_same _ _ _
  have mappedSource := AllocatedLayout.mapped source plan ready domain
  have headerMapped (field : Fin 4) : entered.memaddrs (BitVec.ofNat 64 plan.table + BitVec.ofNat 64 (8 * field.val)) := by
    apply mappedSource .header (8 * field.val) (by omega)
    change 8 * field.val + 8 ≤ 72
    have := field.isLt; omega
  have headerRun := header_executes entered (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 plan.capacity)
    enteredTable enteredKey enteredStride enteredCap headerMapped
  have strideRead : eval allocated stride = some (.val (.word 32#64)) := by
    simp [eval, stride, localVar, evalHOLExact, evalListHOLExact, toExact, allocatedKey,
      valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and]
  refine ⟨(fun target => restore source "t" (restore allocated "stride" target)), ?_⟩
  apply PersistentAlloc.prefix_allocate source _ "t" (.const 72#64)
    (.declare "stride" stride :: headerActions) (fun target => restore allocated "stride" target) plan.table 72 (plan.table + 72) rfl code heapGlobal
    (by have := ready.fits; omega) (Nat.le_refl _) (by omega) (by have := ready.tableAligned; omega) enough
  exact .declare 32#64 strideRead headerRun

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.initial_executes

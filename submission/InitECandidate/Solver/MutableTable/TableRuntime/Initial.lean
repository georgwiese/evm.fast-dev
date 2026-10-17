import InitECandidate.Solver.MutableTable.TableRuntime.Header
import InitECandidate.Solver.WitnessRadix.TableInitial

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix

/-- Actual first allocation, stride declaration and four header stores. -/
def initialState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) : PanSemStateFiniteExact 64 F :=
  headerState (WitnessRadix.QueryBranch.bind (PersistentAlloc.nextState source "t" start (start + 72)) "stride"
    (BitVec.ofNat 64 (NaturalLayout.stride kind))) kind (BitVec.ofNat 64 start) (BitVec.ofNat 64 capacity)

theorem initial_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : NaturalLayout.Valid kind (NaturalLayout.fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (enough : 1 ≤ source.clock) :
    ∃ restoreStack, Executes source TableNew.initialActions (initialState source kind start capacity) restoreStack := by
  let allocated := PersistentAlloc.nextState source "t" start (start + 72)
  let entered := WitnessRadix.QueryBranch.bind allocated "stride" (BitVec.ofNat 64 (NaturalLayout.stride kind))
  have allocatedKey : allocated.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) := by
    unfold allocated PersistentAlloc.nextState
    rw [bind_lookup_other _ "t" "key_len" _ (by decide)]
    exact keyLocal
  have allocatedCap : allocated.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
    unfold allocated PersistentAlloc.nextState
    rw [bind_lookup_other _ "t" "cap" _ (by decide)]
    exact capLocal
  have enteredKey : entered.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) :=
    (bind_lookup_other allocated "stride" "key_len" _ (by decide)).trans allocatedKey
  have enteredCap : entered.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) :=
    (bind_lookup_other allocated "stride" "cap" _ (by decide)).trans allocatedCap
  have enteredTable : entered.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 start))) :=
    (bind_lookup_other allocated "stride" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  have enteredStride : entered.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind)))) := bind_lookup_same _ _ _
  have headerMapped (field : Fin 4) : entered.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 (8 * field.val)) := by
    change source.memaddrs _
    rw [domain]
    have within : 8 * field.val < NaturalLayout.size kind (NaturalLayout.fresh kind start capacity) .header := by
      change 8 * field.val < 72
      have high := field.isLt
      omega
    have actual := NaturalLayout.mapped kind _ valid .header (8 * field.val) within (by omega)
    simpa only [NaturalLayout.cell, NaturalLayout.fresh, BitVec.ofNat_add] using actual
  have headerRun := header_executes entered kind (BitVec.ofNat 64 start) (BitVec.ofNat 64 capacity)
    enteredTable enteredKey enteredStride enteredCap headerMapped
  have strideRead : eval allocated TableNew.stride = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind)))) := by
    cases kind <;> simp [eval, TableNew.stride, localVar, evalHOLExact, evalListHOLExact, toExact, allocatedKey,
      valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, NaturalLayout.stride, KeyHash.keySize]
  have fits : start + 72 ≤ 33806089496 := valid.upper .header
  have aligned : start % 8 = 0 := valid.aligned .header
  refine ⟨(fun target => restore source "t" (restore allocated "stride" target)), ?_⟩
  apply PersistentAlloc.prefix_allocate source _ "t" (.const 72#64)
    (.declare "stride" TableNew.stride :: TableNew.headerActions) (fun target => restore allocated "stride" target)
    start 72 (start + 72) rfl code heapGlobal fits (Nat.le_refl _) (by omega) (by omega) enough
  exact .declare (BitVec.ofNat 64 (NaturalLayout.stride kind)) strideRead headerRun

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.initial_executes

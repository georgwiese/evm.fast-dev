import InitECandidate.Solver.MutableTable.CopyWalk
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

theorem walk_keeps_n {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (selected : List Pool)
    (present : source.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0)))) :
    (walk source kind old next selected).locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))) := by
  induction selected generalizing source with
  | nil => exact present
  | cons pool rest ih => exact ih _ (stage_new_header source kind old next pool (fun _ => present))

theorem walk_result_n {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) :
    (walk source kind old next pools).locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))) := by
  exact walk_keeps_n (stageState source kind old next .header) kind old next [.keys, .values, .used, .order, .position]
    (stage_lookup_same source kind old next .header)

def initial {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "cap" (BitVec.ofNat 64 old.capacity)) "stride" (BitVec.ofNat 64 (stride kind))
def finalState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan) (start : Nat) :=
  walk (initial source kind old) kind old (fresh kind start old.capacity) pools

/-- The entire unchanged htab_copy body, all six actual allocation/copy
stages, five pointer rewrites, final return and lexical restoration. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (nextValid : Valid kind (fresh kind start old.capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64) (header : MemoryModel.Header source.memory kind old count)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : walkPrice kind old (fresh kind start old.capacity) pools ≤ source.clock) :
    ∃ target, evaluateHOLFiniteState source body = (some (.returned (.val (.word (BitVec.ofNat 64 start)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (finalState source kind old start) ∧
      target.clock = source.clock - walkPrice kind old (fresh kind start old.capacity) pools ∧
      MemoryModel.PoolFrame source.memory target.memory kind old := by
  let capped := WitnessRadix.QueryBranch.bind source "cap" (BitVec.ofNat 64 old.capacity)
  let entered := initial source kind old
  let next := fresh kind start old.capacity
  have capRead := MemoryModel.Header.read source kind old oldValid domain count header tableLocal 16 (by decide) (by decide) (BitVec.ofNat 64 old.capacity) (by simp [MemoryModel.headerEntries])
  have cappedT : capped.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "cap" "t" _ (by decide)).trans tableLocal
  have strideRead := MemoryModel.Header.read capped kind old oldValid domain count header cappedT 8 (by decide) (by decide) (BitVec.ofNat 64 (stride kind)) (by simp [MemoryModel.headerEntries])
  have locals : CoreLocals entered kind old := by
    constructor
    · exact (bind_lookup_other _ "stride" "t" _ (by decide)).trans cappedT
    · exact (bind_lookup_other _ "stride" "cap" _ (by decide)).trans (bind_lookup_same _ _ _)
    · exact bind_lookup_same _ _ _
  have allEarlier : ∀ first second, old.base first + size kind old first ≤ next.base second := by
    intro first second
    have ordered := earlier first
    cases second <;> dsimp only [next, fresh] <;> omega
  obtain ⟨restoreStages, stageRuns⟩ := walk_executes entered kind old next oldValid nextValid rfl allEarlier pools (freshEnd kind start old.capacity)
    (fresh_chain kind start old.capacity) domain count header locals (by intro impossible; exact False.elim (impossible rfl)) heap allocCode copyCode enough
  have prefixSetup : Executes source [.declare "cap" (Find.tableLoad 16#64), .declare "stride" (Find.tableLoad 8#64)] entered
      (fun target => restore source "cap" (restore capped "stride" target)) :=
    .declare (BitVec.ofNat 64 old.capacity) capRead (.declare (BitVec.ofNat 64 (stride kind)) strideRead (.done _))
  have setup : Executes source actions (finalState source kind old start)
      (fun target => restore source "cap" (restore capped "stride" (restoreStages target))) := by
    have combined := executes_append prefixSetup stageRuns
    exact combined
  let completed := finalState source kind old start
  have nLocal := walk_result_n entered kind old next
  have nRead : eval completed (localVar "n") = some (.val (.word (BitVec.ofNat 64 start))) := by
    have actual : completed.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 start))) := by
      simpa only [cell, next, fresh, Nat.add_zero, completed, finalState, entered] using nLocal
    simp [eval, localVar, evalHOLExact, toExact, actual]
  have returned : evaluateHOLFiniteState completed (.return (localVar "n")) =
      (some (.returned (.val (.word (BitVec.ofNat 64 start)))), emptyLocalsHOLFinite completed) := by
    simp only [eval] at nRead
    rw [evaluateHOLFiniteState_return, nRead]
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  let output := restore source "cap" (restore capped "stride" (restoreStages (emptyLocalsHOLFinite completed)))
  have restored := restoration_frame setup (emptyLocalsHOLFinite completed)
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) restored
  have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) restored
  refine ⟨output, ?_, ?_, ?_, ?_⟩
  · rw [body_shape, ProgramPrefix.execute setup, returned]
  · exact restored
  · change output.clock = _
    change output.clock = completed.clock at clockEq
    rw [clockEq]
    exact walk_clock entered kind old next pools
  · change MemoryModel.PoolFrame source.memory output.memory kind old
    change output.memory = completed.memory at memoryEq
    rw [memoryEq]
    exact walk_preserves_old entered kind old next oldValid nextValid rfl allEarlier pools

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_keeps_n
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_result_n
#print axioms InitECandidate.Solver.MutableTable.TableCopy.execute

import InitECandidate.Solver.MutableTable.TableRuntime.Contexts
import InitECandidate.Solver.WitnessRadix.TableExecution

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix
open NaturalLayout

def enteredState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  finishState (usedState (initialState source kind start capacity) kind start capacity) kind start capacity

abbrev price := TableNew.price

theorem setup {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price capacity ≤ source.clock) :
    ∃ restoreStack, Executes source TableNew.actions (enteredState source kind start capacity) restoreStack := by
  have enough' : TableNew.clearCost capacity + 6 ≤ source.clock := enough
  obtain ⟨restoreInitial, initialRun⟩ := initial_executes source kind start capacity valid domain keyLocal capLocal heapGlobal allocCode (by omega)
  let initial := initialState source kind start capacity
  have localsInitial := initial_locals source kind start capacity capLocal
  have heapInitial : initial.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72)))) :=
    TableNew.allocated_heap source "t" start (start + 72)
  obtain ⟨restorePreclear, preclearRun⟩ := preclear_executes initial kind start capacity valid domain localsInitial heapInitial allocCode
    (by change 3 ≤ source.clock - 1; omega)
  let beforeClear := usedState initial kind start capacity
  have localsBefore := preclear_locals initial kind start capacity localsInitial
  have heapBefore : beforeClear.globals.lookup (ofString "heap_ptr") = some (.val (.word
      (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))) :=
    TableNew.allocated_heap (valsStored initial kind start capacity) "used"
      (start + 72 + stride kind * capacity + 8 * capacity)
      (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)
  have usedLocal : beforeClear.locals.lookup (ofString "used") = some (.val (.word (usedAddress kind start capacity))) := bind_lookup_same _ _ _
  obtain ⟨restoreFinish, finishRun⟩ := finish_executes beforeClear kind start capacity valid domain capacityShape localsBefore usedLocal heapBefore allocCode zeroCode
    (by change TableNew.clearCost capacity + 2 ≤ source.clock - 1 - 1 - 1 - 1; omega)
  refine ⟨(fun target => restoreInitial (restorePreclear (restoreFinish target))), ?_⟩
  rw [TableNew.actions_split]
  have firstCombined := executes_append initialRun preclearRun
  have combined := executes_append firstCombined finishRun
  exact combined

/-- Entire unchanged persistent htab_new, for every original key width:
all six allocations, used clear, nine header stores, table return and scopes.
The exact layout/clock/code/cursor premises are explicit. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price capacity ≤ source.clock) :
    ∃ target, evaluateHOLFiniteState source TableNew.body = (some (.returned (.val (.word (BitVec.ofNat 64 start)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (enteredState source kind start capacity) := by
  classical
  obtain ⟨restoreStack, execution⟩ := setup source kind start capacity valid domain capacityShape keyLocal capLocal heapGlobal allocCode zeroCode enough
  have localsInitial := initial_locals source kind start capacity capLocal
  have localsBefore := preclear_locals (initialState source kind start capacity) kind start capacity localsInitial
  have localsFinal := finish_locals _ kind start capacity localsBefore
  have tableLocal : (enteredState source kind start capacity).locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 start))) := localsFinal.tableLocal
  have returned : evaluateHOLFiniteState (enteredState source kind start capacity) TableNew.returnTable =
      (some (.returned (.val (.word (BitVec.ofNat 64 start)))), emptyLocalsHOLFinite (enteredState source kind start capacity)) := by
    simp [TableNew.returnTable, evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, tableLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have whole := ProgramPrefix.execute execution TableNew.returnTable
  rw [returned] at whole
  refine ⟨restoreStack (emptyLocalsHOLFinite (enteredState source kind start capacity)), ?_, ?_⟩
  · rw [TableNew.body_shape]
    exact whole
  · exact restoration_frame execution _

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.setup
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.execute

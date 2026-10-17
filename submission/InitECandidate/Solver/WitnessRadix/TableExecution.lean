import InitECandidate.Solver.WitnessRadix.TableContexts
import InitECandidate.Solver.WitnessRadix.ProgramPrefixAppend

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def enteredState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  finishState (preClearState (initialState source plan) plan) plan
def price (capacity : Nat) : Nat := clearCost capacity + 6

theorem actions_split : actions = initialActions ++ preClearActions ++ finishActions := by
  simp only [actions, initialActions, preClearActions, finishActions, headerActions, clearCall,
    List.cons_append, List.nil_append]

theorem setup {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price plan.capacity ≤ source.clock) :
    ∃ restoreStack, Executes source actions (enteredState source plan) restoreStack := by
  have enough' : clearCost plan.capacity + 6 ≤ source.clock := enough
  obtain ⟨restoreInitial, initialRun⟩ := initial_executes source plan ready domain keyLocal capLocal heapGlobal allocCode (by omega)
  let initial := initialState source plan
  have localsInitial := initial_locals source plan capLocal
  have heapInitial : initial.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72)))) :=
    allocated_heap source "t" plan.table (plan.table + 72)
  obtain ⟨restorePreclear, preclearRun⟩ := preclear_executes initial plan ready domain localsInitial heapInitial allocCode
    (by change 3 ≤ source.clock - 1; omega)
  let beforeClear := preClearState initial plan
  have localsBefore := preclear_locals initial plan localsInitial
  have heapBefore : beforeClear.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)))) :=
    allocated_heap (valsStored initial plan) "used" (plan.table + 72 + 40 * plan.capacity)
      (plan.table + 72 + 41 * plan.capacity + plan.padding)
  have usedLocal : beforeClear.locals.lookup (ofString "used") = some (.val (.word (usedAddress plan))) := bind_lookup_same _ _ _
  obtain ⟨restoreFinish, finishRun⟩ := finish_executes beforeClear plan ready domain capacityShape localsBefore usedLocal heapBefore allocCode zeroCode
    (by change clearCost plan.capacity + 2 ≤ source.clock - 1 - 1 - 1 - 1; omega)
  refine ⟨(fun target => restoreInitial (restorePreclear (restoreFinish target))), ?_⟩
  rw [actions_split]
  have firstCombined := executes_append initialRun preclearRun
  have combined := executes_append firstCombined finishRun
  exact combined

/-- Complete fixed htab_new for 32-byte keys, including all six actual
allocations, used clearing, all nine header stores, scopes and table return. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : price plan.capacity ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (enteredState source plan) := by
  classical
  obtain ⟨restoreStack, execution⟩ := setup source plan ready domain capacityShape keyLocal capLocal heapGlobal allocCode zeroCode enough
  have localsInitial := initial_locals source plan capLocal
  have localsBefore := preclear_locals (initialState source plan) plan localsInitial
  have localsFinal := finish_locals _ plan localsBefore
  have tableLocal : (enteredState source plan).locals.lookup (ofString "t") =
      some (.val (.word (BitVec.ofNat 64 plan.table))) := localsFinal.tableLocal
  have returned : evaluateHOLFiniteState (enteredState source plan) returnTable =
      (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), emptyLocalsHOLFinite (enteredState source plan)) := by
    simp [returnTable, evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact,
      tableLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have whole := ProgramPrefix.execute execution returnTable
  rw [returned] at whole
  refine ⟨restoreStack (emptyLocalsHOLFinite (enteredState source plan)), ?_, ?_⟩
  · rw [body_shape]; exact whole
  · exact restoration_frame execution (emptyLocalsHOLFinite (enteredState source plan))

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.setup
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.execute

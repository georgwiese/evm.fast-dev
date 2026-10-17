import InitECandidate.Solver.WitnessRadix.TableClear
import InitECandidate.Solver.WitnessRadix.TablePreClear

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def finishActions : List Action :=
  [.command clearCall, .command (headerStore 48#64 (localVar "used")),
   .allocate "order" (capacityTimes (.const 8#64)), .command (headerStore 56#64 (localVar "order")),
   .allocate "order_pos" (capacityTimes (.const 8#64)), .command (headerStore 64#64 (localVar "order_pos"))]
def usedStored {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  let cleared := clearState source plan
  { cleared with memory := StoreWord.put cleared.memory (BitVec.ofNat 64 plan.table + 48#64) (usedAddress plan) }
def orderState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  PersistentAlloc.nextState (usedStored source plan) "order" (plan.table + 72 + 41 * plan.capacity + plan.padding)
    (plan.table + 72 + 49 * plan.capacity + plan.padding)
def orderStored {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  let allocated := orderState source plan
  { allocated with memory := (StoreWord.put allocated.memory (BitVec.ofNat 64 plan.table + 56#64)
    (BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding))) }
def backupState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  PersistentAlloc.nextState (orderStored source plan) "order_pos" (plan.table + 72 + 49 * plan.capacity + plan.padding)
    (plan.table + 72 + 57 * plan.capacity + plan.padding)
def finishState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  let allocated := backupState source plan
  { allocated with memory := (StoreWord.put allocated.memory (BitVec.ofNat 64 plan.table + 64#64)
    (BitVec.ofNat 64 (plan.table + 72 + 49 * plan.capacity + plan.padding))) }

theorem finish_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (locals : Locals source (BitVec.ofNat 64 plan.table) plan.capacity)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (usedAddress plan))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : clearCost plan.capacity + 2 ≤ source.clock) :
    ∃ restoreStack, Executes source finishActions (finishState source plan) restoreStack := by
  have fits := ready.fits
  have tableAligned := ready.tableAligned
  have padded := ready.padded
  have clearedLocals : Locals (clearState source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  have storedLocals : Locals (usedStored source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  have orderLocals : Locals (orderState source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    locals_allocated (usedStored source plan) _ _ storedLocals "order" _ _ (by decide) (by decide) (by decide)
  have storedOrderLocals : Locals (orderStored source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    ⟨orderLocals.tableLocal, orderLocals.capLocal, orderLocals.strideLocal⟩
  have backupLocals : Locals (backupState source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    locals_allocated (orderStored source plan) _ _ storedOrderLocals "order_pos" _ _ (by decide) (by decide) (by decide)
  have orderLocal : (orderState source plan).locals.lookup (ofString "order") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)))) := bind_lookup_same _ _ _
  have backupLocal : (backupState source plan).locals.lookup (ofString "order_pos") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72 + 49 * plan.capacity + plan.padding)))) := bind_lookup_same _ _ _
  have mapped := AllocatedLayout.mapped source plan ready domain
  have usedMapped : (clearState source plan).memaddrs (BitVec.ofNat 64 plan.table + 48#64) :=
    mapped .header 48 (by decide) (by change 48 + 8 ≤ 72; decide)
  have orderMapped : (orderState source plan).memaddrs (BitVec.ofNat 64 plan.table + 56#64) :=
    mapped .header 56 (by decide) (by change 56 + 8 ≤ 72; decide)
  have backupMapped : (backupState source plan).memaddrs (BitVec.ofNat 64 plan.table + 64#64) :=
    mapped .header 64 (by decide) (by change 64 + 8 ≤ 72; decide)
  have clearRun := clear_execute source plan ready domain capacityShape usedLocal locals.capLocal zeroCode (by omega)
  have usedRun := header_store (clearState source plan) _ 48#64 (usedAddress plan) (localVar "used") locals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, clearState, usedLocal]) usedMapped
  have orderRun := header_store (orderState source plan) _ 56#64
    (BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)) (localVar "order") orderLocals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, orderLocal]) orderMapped
  have backupRun := header_store (backupState source plan) _ 64#64
    (BitVec.ofNat 64 (plan.table + 72 + 49 * plan.capacity + plan.padding)) (localVar "order_pos") backupLocals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, backupLocal]) backupMapped
  refine ⟨(fun target => restore (usedStored source plan) "order" (restore (orderStored source plan) "order_pos" target)), ?_⟩
  apply Executes.command clearRun (by change source.clock - clearCost plan.capacity ≤ source.clock; omega)
  apply Executes.command usedRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (usedStored source plan) _ "order" (capacityTimes (.const 8#64)) _ _
    (plan.table + 72 + 41 * plan.capacity + plan.padding) (8 * plan.capacity)
    (plan.table + 72 + 49 * plan.capacity + plan.padding)
    (read_scale (usedStored source plan) _ _ 8 storedLocals) allocCode heapGlobal
    (by omega) (by omega) (by omega) (by omega) (by change 1 ≤ source.clock - clearCost plan.capacity; omega)
  apply Executes.command orderRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (orderStored source plan) _ "order_pos" (capacityTimes (.const 8#64)) _ _
    (plan.table + 72 + 49 * plan.capacity + plan.padding) (8 * plan.capacity)
    (plan.table + 72 + 57 * plan.capacity + plan.padding)
    (read_scale (orderStored source plan) _ _ 8 storedOrderLocals) allocCode
    (allocated_heap (usedStored source plan) "order" (plan.table + 72 + 41 * plan.capacity + plan.padding)
      (plan.table + 72 + 49 * plan.capacity + plan.padding))
    (by omega) (by omega) (by omega) (by omega) (by change 1 ≤ source.clock - clearCost plan.capacity - 1; omega)
  exact .command backupRun (Nat.le_refl _) (.done _)

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.finish_executes

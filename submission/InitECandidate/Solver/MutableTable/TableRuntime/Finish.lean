import InitECandidate.Solver.MutableTable.TableRuntime.Clear
import InitECandidate.Solver.WitnessRadix.TableFinish

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix
open NaturalLayout

def usedStored {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  let cleared := clearState source kind start capacity
  {cleared with memory := StoreWord.put cleared.memory (BitVec.ofNat 64 start + 48#64) (usedAddress kind start capacity)}
def orderState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (usedStored source kind start capacity) "order"
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
def orderStored {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  let allocated := orderState source kind start capacity
  {allocated with memory := (StoreWord.put allocated.memory (BitVec.ofNat 64 start + 56#64)
    (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))}
def backupState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (orderStored source kind start capacity) "order_pos"
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
    (freshEnd kind start capacity)
def finishState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  let allocated := backupState source kind start capacity
  {allocated with memory := (StoreWord.put allocated.memory (BitVec.ofNat 64 start + 64#64)
    (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)))}

/-- The real clear, final two allocations and three header stores. Their
rounding/guards/maps follow from fresh pool ownership, for every key width. -/
theorem finish_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (usedAddress kind start capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word
      (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : TableNew.clearCost capacity + 2 ≤ source.clock) :
    ∃ restoreStack, Executes source TableNew.finishActions (finishState source kind start capacity) restoreStack := by
  have orderFits : start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity ≤ 33806089496 := valid.upper .order
  have positionFits : freshEnd kind start capacity ≤ 33806089496 := valid.upper .position
  have positionAligned : (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) % 8 = 0 := valid.aligned .position
  have finalAligned : freshEnd kind start capacity % 8 = 0 := by
    dsimp only [freshEnd]
    omega
  have storedLocals : Locals (usedStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  have orderLocals : Locals (orderState source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    Locals.allocated (usedStored source kind start capacity) kind _ capacity storedLocals "order" _ _ (by decide) (by decide) (by decide)
  have storedOrderLocals : Locals (orderStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    ⟨orderLocals.tableLocal, orderLocals.capLocal, orderLocals.strideLocal⟩
  have backupLocals : Locals (backupState source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    Locals.allocated (orderStored source kind start capacity) kind _ capacity storedOrderLocals "order_pos" _ _ (by decide) (by decide) (by decide)
  have orderLocal : (orderState source kind start capacity).locals.lookup (ofString "order") = some (.val (.word
      (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))) := bind_lookup_same _ _ _
  have backupLocal : (backupState source kind start capacity).locals.lookup (ofString "order_pos") = some (.val (.word
      (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)))) := bind_lookup_same _ _ _
  have headerMapped (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) : source.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) := by
    rw [domain]
    simpa only [cell, fresh, BitVec.ofNat_add] using mapped kind (fresh kind start capacity) valid .header offset inside aligned
  have clearRun := clear_execute source kind start capacity valid domain capacityShape usedLocal locals.capLocal zeroCode (by omega)
  have usedRun := TableNew.header_store (clearState source kind start capacity) (BitVec.ofNat 64 start) 48#64 (usedAddress kind start capacity)
    (localVar "used") locals.tableLocal (by simp [eval, localVar, evalHOLExact, toExact, clearState, usedLocal]) (headerMapped 48 (by decide) (by decide))
  have orderRun := TableNew.header_store (orderState source kind start capacity) (BitVec.ofNat 64 start) 56#64
    (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)) (localVar "order") orderLocals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, orderLocal]) (headerMapped 56 (by decide) (by decide))
  have backupRun := TableNew.header_store (backupState source kind start capacity) (BitVec.ofNat 64 start) 64#64
    (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)) (localVar "order_pos") backupLocals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, backupLocal]) (headerMapped 64 (by decide) (by decide))
  refine ⟨(fun target => restore (usedStored source kind start capacity) "order" (restore (orderStored source kind start capacity) "order_pos" target)), ?_⟩
  apply Executes.command clearRun (by change source.clock - TableNew.clearCost capacity ≤ source.clock; omega)
  apply Executes.command usedRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (usedStored source kind start capacity) _ "order" (TableNew.capacityTimes (.const 8#64)) _ _
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity) (8 * capacity)
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
    (read_scale _ kind _ capacity 8 storedLocals) allocCode heapGlobal orderFits (Nat.le_refl _) (by omega) positionAligned
    (by change 1 ≤ source.clock - TableNew.clearCost capacity; omega)
  apply Executes.command orderRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (orderStored source kind start capacity) _ "order_pos" (TableNew.capacityTimes (.const 8#64)) _ _
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) (8 * capacity) (freshEnd kind start capacity)
    (read_scale _ kind _ capacity 8 storedOrderLocals) allocCode
    (TableNew.allocated_heap (usedStored source kind start capacity) "order"
      (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)
      (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity))
    positionFits (Nat.le_refl _) (by dsimp only [freshEnd]; omega) finalAligned
    (by change 1 ≤ source.clock - TableNew.clearCost capacity - 1; omega)
  exact .command backupRun (Nat.le_refl _) (.done _)

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.finish_executes

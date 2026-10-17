import InitECandidate.Solver.MutableTable.TableRuntime.Locals
import InitECandidate.Solver.WitnessRadix.TablePreClear

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix
open NaturalLayout

def keysState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState source "keys" (start + 72) (start + 72 + stride kind * capacity)
def keysStored {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  let allocated := keysState source kind start capacity
  {allocated with memory := StoreWord.put allocated.memory (BitVec.ofNat 64 start + 32#64) (BitVec.ofNat 64 (start + 72))}
def valsState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (keysStored source kind start capacity) "vals"
    (start + 72 + stride kind * capacity) (start + 72 + stride kind * capacity + 8 * capacity)
def valsStored {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  let allocated := valsState source kind start capacity
  {allocated with memory := StoreWord.put allocated.memory (BitVec.ofNat 64 start + 40#64) (BitVec.ofNat 64 (start + 72 + stride kind * capacity))}
def usedState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (valsStored source kind start capacity) "used"
    (start + 72 + stride kind * capacity + 8 * capacity)
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)

/-- Three real array allocations and two header stores up to memzero. All
allocator room/rounding and field mappings follow from fresh pool geometry. -/
theorem preclear_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72)))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (enough : 3 ≤ source.clock) :
    ∃ restoreStack, Executes source TableNew.preClearActions (usedState source kind start capacity) restoreStack := by
  have keyFits : start + 72 + stride kind * capacity ≤ 33806089496 := valid.upper .keys
  have valsFits : start + 72 + stride kind * capacity + 8 * capacity ≤ 33806089496 := valid.upper .values
  have usedFits : start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 := valid.upper .used
  have keyAligned : (start + 72 + stride kind * capacity) % 8 = 0 := valid.aligned .values
  have valsAligned : (start + 72 + stride kind * capacity + 8 * capacity) % 8 = 0 := valid.aligned .used
  have usedAligned : (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity) % 8 = 0 := valid.aligned .order
  have roundBounds := rounded_bounds capacity
  have localsKeys := Locals.allocated source kind _ capacity locals "keys" (start + 72) (start + 72 + stride kind * capacity) (by decide) (by decide) (by decide)
  have localsKeysStored : Locals (keysStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    ⟨localsKeys.tableLocal, localsKeys.capLocal, localsKeys.strideLocal⟩
  have localsVals := Locals.allocated (keysStored source kind start capacity) kind _ capacity localsKeysStored "vals"
    (start + 72 + stride kind * capacity) (start + 72 + stride kind * capacity + 8 * capacity) (by decide) (by decide) (by decide)
  have localsValsStored : Locals (valsStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity :=
    ⟨localsVals.tableLocal, localsVals.capLocal, localsVals.strideLocal⟩
  have keyLocal : (keysState source kind start capacity).locals.lookup (ofString "keys") = some (.val (.word (BitVec.ofNat 64 (start + 72)))) := bind_lookup_same _ _ _
  have valLocal : (valsState source kind start capacity).locals.lookup (ofString "vals") = some (.val (.word (BitVec.ofNat 64 (start + 72 + stride kind * capacity)))) := bind_lookup_same _ _ _
  have headerMapped (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) : source.memaddrs (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) := by
    rw [domain]
    simpa only [cell, fresh, BitVec.ofNat_add] using mapped kind (fresh kind start capacity) valid .header offset inside aligned
  have keyRun := TableNew.header_store (keysState source kind start capacity) (BitVec.ofNat 64 start) 32#64 (BitVec.ofNat 64 (start + 72))
    (localVar "keys") localsKeys.tableLocal (by simp [eval, localVar, evalHOLExact, toExact, keyLocal]) (headerMapped 32 (by decide) (by decide))
  have valRun := TableNew.header_store (valsState source kind start capacity) (BitVec.ofNat 64 start) 40#64 (BitVec.ofNat 64 (start + 72 + stride kind * capacity))
    (localVar "vals") localsVals.tableLocal (by simp [eval, localVar, evalHOLExact, toExact, valLocal]) (headerMapped 40 (by decide) (by decide))
  refine ⟨(fun target => restore source "keys" (restore (keysStored source kind start capacity) "vals"
    (restore (valsStored source kind start capacity) "used" target))), ?_⟩
  apply PersistentAlloc.prefix_allocate source _ "keys" (TableNew.capacityTimes (localVar "stride")) _ _
    (start + 72) (stride kind * capacity) (start + 72 + stride kind * capacity)
    (read_key_amount source kind _ capacity locals) code heapGlobal keyFits (Nat.le_refl _) (by omega) keyAligned (by omega)
  apply Executes.command keyRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (keysStored source kind start capacity) _ "vals" (TableNew.capacityTimes (.const 8#64)) _ _
    (start + 72 + stride kind * capacity) (8 * capacity) (start + 72 + stride kind * capacity + 8 * capacity)
    (read_scale _ kind _ capacity 8 localsKeysStored) code (TableNew.allocated_heap source "keys" (start + 72) (start + 72 + stride kind * capacity)) valsFits (Nat.le_refl _) (by omega) valsAligned
    (by change 1 ≤ source.clock - 1; omega)
  apply Executes.command valRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (valsStored source kind start capacity) _ "used" (localVar "cap") [] id
    (start + 72 + stride kind * capacity + 8 * capacity) capacity (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)
    (read_capacity _ kind _ capacity localsValsStored) code (TableNew.allocated_heap (keysStored source kind start capacity) "vals"
      (start + 72 + stride kind * capacity) (start + 72 + stride kind * capacity + 8 * capacity))
    (by omega) (by omega) (by omega) usedAligned (by change 1 ≤ source.clock - 1 - 1; omega)
  exact .done _

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.preclear_executes

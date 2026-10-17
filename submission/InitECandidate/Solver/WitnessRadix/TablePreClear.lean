import InitECandidate.Solver.WitnessRadix.TableLocals

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def preClearActions : List Action :=
  [.allocate "keys" (capacityTimes (localVar "stride")), .command (headerStore 32#64 (localVar "keys")),
   .allocate "vals" (capacityTimes (.const 8#64)), .command (headerStore 40#64 (localVar "vals")),
   .allocate "used" (localVar "cap")]
def keysState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  PersistentAlloc.nextState source "keys" (plan.table + 72) (plan.table + 72 + 32 * plan.capacity)
def keysStored {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  let allocated := keysState source plan
  { allocated with memory := StoreWord.put allocated.memory (BitVec.ofNat 64 plan.table + 32#64) (BitVec.ofNat 64 (plan.table + 72)) }
def valsState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  PersistentAlloc.nextState (keysStored source plan) "vals" (plan.table + 72 + 32 * plan.capacity) (plan.table + 72 + 40 * plan.capacity)
def valsStored {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  let allocated := valsState source plan
  { allocated with memory := (StoreWord.put allocated.memory (BitVec.ofNat 64 plan.table + 40#64)
      (BitVec.ofNat 64 (plan.table + 72 + 32 * plan.capacity))) }
def preClearState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  PersistentAlloc.nextState (valsStored source plan) "used" (plan.table + 72 + 40 * plan.capacity)
    (plan.table + 72 + 41 * plan.capacity + plan.padding)

/-- Actual key/value/used allocations and their two header installations.
The only writes are the real header cells, with exactly three call clocks. -/
theorem preclear_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (locals : Locals source (BitVec.ofNat 64 plan.table) plan.capacity)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (plan.table + 72)))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (enough : 3 ≤ source.clock) :
    ∃ restoreStack, Executes source preClearActions (preClearState source plan) restoreStack := by
  have fits := ready.fits
  have tableAligned := ready.tableAligned
  have padded := ready.padded
  have paddingBound := ready.paddingBound
  have localsKeys : Locals (keysState source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    locals_allocated source _ _ locals "keys" _ _ (by decide) (by decide) (by decide)
  have localsKeysStored : Locals (keysStored source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    ⟨localsKeys.tableLocal, localsKeys.capLocal, localsKeys.strideLocal⟩
  have localsVals : Locals (valsState source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    locals_allocated (keysStored source plan) _ _ localsKeysStored "vals" _ _ (by decide) (by decide) (by decide)
  have localsValsStored : Locals (valsStored source plan) (BitVec.ofNat 64 plan.table) plan.capacity :=
    ⟨localsVals.tableLocal, localsVals.capLocal, localsVals.strideLocal⟩
  have keyLocal : (keysState source plan).locals.lookup (ofString "keys") = some (.val (.word (BitVec.ofNat 64 (plan.table + 72)))) :=
    bind_lookup_same _ _ _
  have valLocal : (valsState source plan).locals.lookup (ofString "vals") =
      some (.val (.word (BitVec.ofNat 64 (plan.table + 72 + 32 * plan.capacity)))) := bind_lookup_same _ _ _
  have mapped := AllocatedLayout.mapped source plan ready domain
  have keyMapped : (keysState source plan).memaddrs (BitVec.ofNat 64 plan.table + 32#64) :=
    mapped .header 32 (by decide) (by change 32 + 8 ≤ 72; decide)
  have valMapped : (valsState source plan).memaddrs (BitVec.ofNat 64 plan.table + 40#64) :=
    mapped .header 40 (by decide) (by change 40 + 8 ≤ 72; decide)
  have keyRun := header_store (keysState source plan) (BitVec.ofNat 64 plan.table) 32#64 (BitVec.ofNat 64 (plan.table + 72)) (localVar "keys") localsKeys.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, keyLocal]) keyMapped
  have valRun := header_store (valsState source plan) (BitVec.ofNat 64 plan.table) 40#64 (BitVec.ofNat 64 (plan.table + 72 + 32 * plan.capacity)) (localVar "vals") localsVals.tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, valLocal]) valMapped
  refine ⟨(fun target => restore source "keys" (restore (keysStored source plan) "vals"
    (restore (valsStored source plan) "used" target))), ?_⟩
  apply PersistentAlloc.prefix_allocate source _ "keys" (capacityTimes (localVar "stride")) _ _
    (plan.table + 72) (32 * plan.capacity) (plan.table + 72 + 32 * plan.capacity)
    (read_key_amount source _ _ locals) code heapGlobal (by omega) (Nat.le_refl _) (by omega) (by omega) (by omega)
  apply Executes.command keyRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (keysStored source plan) _ "vals" (capacityTimes (.const 8#64)) _ _
    (plan.table + 72 + 32 * plan.capacity) (8 * plan.capacity) (plan.table + 72 + 40 * plan.capacity)
    (read_scale (keysStored source plan) _ _ 8 localsKeysStored) code
    (allocated_heap source "keys" (plan.table + 72) (plan.table + 72 + 32 * plan.capacity)) (by omega) (by omega) (by omega) (by omega)
    (by change 1 ≤ source.clock - 1; omega)
  apply Executes.command valRun (Nat.le_refl _)
  apply PersistentAlloc.prefix_allocate (valsStored source plan) _ "used" (localVar "cap") [] id
    (plan.table + 72 + 40 * plan.capacity) plan.capacity (plan.table + 72 + 41 * plan.capacity + plan.padding)
    (read_capacity (valsStored source plan) _ _ localsValsStored) code
    (allocated_heap (keysStored source plan) "vals" (plan.table + 72 + 32 * plan.capacity) (plan.table + 72 + 40 * plan.capacity)) (by omega) (by omega) (by omega) (by omega)
    (by change 1 ≤ source.clock - 1 - 1; omega)
  exact .done _

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.preclear_executes

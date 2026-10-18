import InitECandidate.Solver.GasBudget.WarmAccounts
import InitECandidate.Solver.GasBudget.WarmTablesProgram
import InitECandidate.Solver.GasBudget.WarmKeysConstructorNormal
import InitECandidate.Solver.MutableTable.MemoryModelBeforeFloor

namespace InitECandidate.Solver.GasBudget.WarmTables
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def price (addresses keys : Nat) : Nat :=
  (1805 + WarmPrecompiles.price 19 addresses + WarmKeys.price 0 keys +
    GrowRuntime.growthPotential .account (max 64 (4 * (addresses + 20))) +
    GrowRuntime.growthPotential .storage (max 16 (4 * (keys + 1)))) -
    (GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16)

/-- Eliminate the final-capacity potentials using the actual population
high-water bounds. This is a finite source-clock phase price, not target K. -/
theorem price_bound (paid accountCapacity storageCapacity addresses keys : Nat)
    (budget : paid + GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16 ≤
      1805 + WarmPrecompiles.price 19 addresses + WarmKeys.price 0 keys +
      GrowRuntime.growthPotential .account accountCapacity + GrowRuntime.growthPotential .storage storageCapacity)
    (account : accountCapacity ≤ max 64 (4 * (addresses + 20))) (storage : storageCapacity ≤ max 16 (4 * (keys + 1))) :
    paid ≤ price addresses keys := by
  have first := GrowRuntime.potential_mono .account _ _ account
  have second := GrowRuntime.potential_mono .storage _ _ storage
  unfold price
  omega

/-- Both original transaction warm tables, in their actual enclosing
scopes. The account table survives all subsequent storage allocations and
growth; both live physical models share the final heap cursor and are
separated. Earlier message words and unrelated caller bindings survive. -/
theorem normal_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (cursor addressesStart addressCount keysStart keyCount : Nat) (sender : BitVec 64) (pointers : Nat → BitVec 64) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ cursor) (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (precompileStart : Nat) (precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩)
    (array : PointerArray source.memory 20 addressesStart addressCount cursor pointers) (positive : 0 < addressCount)
    (keyRegion : MemoryRegion.Valid (WarmKeys.inputRegion keysStart keyCount))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (precompiles : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 addressesStart))))
    (countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (addressCount - 1)))))
    (keysLocal : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart))))
    (keyCountLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount))))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one))
    (normal : evaluateHOLFiniteState source WarmPrecompiles.constructorSite = (some (.returned value), post)) :
    ∃ paid accountPlan storagePlan accountSlots storageSlots nextCursor storageStart entered warmed finish,
      paid ≤ source.clock ∧ paid ≤ price addressCount keyCount ∧ warmed.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16 ≤
        1805 + WarmPrecompiles.price 19 addressCount + WarmKeys.price 0 keyCount + GrowRuntime.growthPotential .account accountPlan.capacity + GrowRuntime.growthPotential .storage storagePlan.capacity ∧
      TableState warmed .account accountPlan accountSlots nextCursor cursor ∧ TableState warmed .storage storagePlan storageSlots nextCursor storageStart ∧
      (∀ first second, accountPlan.base first + size .account accountPlan first ≤ storagePlan.base second) ∧
      accountSlots.length ≤ 19 + addressCount ∧ storageSlots.length ≤ keyCount ∧
      accountPlan.capacity ≤ max 64 (4 * (addressCount + 20)) ∧ storagePlan.capacity ≤ max 16 (4 * (keyCount + 1)) ∧
      warmed.locals.lookup (ofString "aa") = some (.val (.word (cell accountPlan .header 0))) ∧
      WarmKeys.Locals warmed (cell storagePlan .header 0) keysStart keyCount keyCount ∧ WarmKeys.Environment warmed ∧
      evaluateHOLFiniteState warmed WarmKeys.afterLoop = (some (.returned value), finish) ∧
      post = restore source "aa" (restore entered "ak" finish) ∧ warmed.code = source.code ∧
      HeapGlobals source warmed ∧
      PointerArray warmed.memory 20 addressesStart addressCount cursor pointers ∧
      (∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address) ∧
      ∀ key : MlS, key ≠ ofString "aa" → key ≠ ofString "ak" → key ≠ ofString "i" → warmed.locals.lookup key = source.locals.lookup key := by
  obtain ⟨accountPaid, accountPlan, accountSlots, storageStart, entered, accountFinish, accountFits, accountClock, accountBound,
    accountTable, accountEnvironment, accountArray, accountLocals, accountCount, accountCapacity, accountRun, accountRestored, accountCodes, accountGlobals, accountProtected, accountLocalFrame⟩ :=
    WarmAccounts.normal_bound source post value cursor addressesStart addressCount sender pointers environment lower bounded aligned precompileStart precompileValid array positive
      heap precompiles senderLocal addressesLocal countLocal queryFits queryMapped newCode normal
  have forward : cursor ≤ storageStart := by
    have low := accountTable.lower .header
    have before := accountTable.earlier .header
    change accountPlan.base .header + 72 ≤ storageStart at before
    omega
  rw [storage_entry] at accountRun
  rw [WitnessRadix.StateSteps.next_sequence entered entered .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _)] at accountRun
  have storedKeys : entered.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart))) :=
    (accountLocalFrame _ (by decide) (by decide)).trans keysLocal
  have storedCount : entered.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount))) :=
    (accountLocalFrame _ (by decide) (by decide)).trans keyCountLocal
  have constructorCode : entered.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one) := by rw [accountCodes]; exact newCode
  obtain ⟨storagePaid, storagePlan, storageSlots, nextCursor, warmed, finish, storageFits, storageClock, storageBound, storageTable, finalEnvironment,
    finalLocals, storageCount, storageCapacity, restRun, storageRestored, storageCodes, storageGlobals, storageProtected, storageLocalFrame⟩ :=
    WarmKeys.constructor_normal_bound entered accountFinish value storageStart keysStart keyCount accountEnvironment (by omega) accountTable.bounded accountTable.aligned
      keyRegion accountTable.heap storedKeys storedCount constructorCode accountRun
  have pools := MemoryModel.PoolFrame.of_protected_before entered.memory warmed.memory .account accountPlan accountTable.valid storageStart accountTable.earlier storageProtected
  have header := MemoryModel.Header.of_pool_frame entered.memory warmed.memory .account accountPlan _ accountTable.header pools
  have domain : warmed.memaddrs = entered.memaddrs := finalEnvironment.domain.trans accountEnvironment.domain.symm
  have endian : warmed.be = entered.be := finalEnvironment.little.trans accountEnvironment.little.symm
  have occupied := MemoryModel.Occupied.of_pool_frame entered warmed .account accountPlan accountTable.valid accountSlots accountTable.occupied domain endian pools
  have cursorForward : storageStart ≤ nextCursor := by
    have low := storageTable.lower .header
    have before := storageTable.earlier .header
    change storagePlan.base .header + 72 ≤ nextCursor at before
    omega
  have finalAccountTable : TableState warmed .account accountPlan accountSlots nextCursor cursor :=
    ⟨accountTable.valid, accountTable.half, header, occupied, accountTable.power, storageTable.heap, storageTable.bounded, storageTable.aligned,
      (by intro pool; have before := accountTable.earlier pool; omega), accountTable.lower⟩
  have finalProtected : ∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address := by
    intro address before
    exact (storageProtected address (by omega)).trans (accountProtected address before)
  have combined : accountPaid + storagePaid + GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16 ≤
      1805 + WarmPrecompiles.price 19 addressCount + WarmKeys.price 0 keyCount + GrowRuntime.growthPotential .account accountPlan.capacity + GrowRuntime.growthPotential .storage storagePlan.capacity := by omega
  have totalPrice := price_bound (accountPaid + storagePaid) accountPlan.capacity storagePlan.capacity addressCount keyCount combined accountCapacity storageCapacity
  refine ⟨accountPaid + storagePaid, accountPlan, storagePlan, accountSlots, storageSlots, nextCursor, storageStart, entered, warmed, finish,
    by omega, totalPrice, by omega, combined, finalAccountTable, storageTable, ?_, accountCount, storageCount, accountCapacity, storageCapacity, ?_,
    finalLocals, finalEnvironment, restRun, ?_, storageCodes.trans accountCodes, accountGlobals.trans storageGlobals, array.of_protected finalProtected, finalProtected, ?_⟩
  · intro first second
    have before := accountTable.earlier first
    have after := storageTable.lower second
    omega
  · exact (storageLocalFrame _ (by decide) (by decide)).trans accountLocals.table
  · rw [storageRestored] at accountRestored
    exact accountRestored
  · intro key notAccount notStorage notIndex
    exact (storageLocalFrame key notStorage notIndex).trans (accountLocalFrame key notAccount notIndex)

end InitECandidate.Solver.GasBudget.WarmTables

#print axioms InitECandidate.Solver.GasBudget.WarmTables.normal_bound

#print axioms InitECandidate.Solver.GasBudget.WarmTables.price_bound

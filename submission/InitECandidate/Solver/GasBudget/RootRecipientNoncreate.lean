import InitECandidate.Solver.GasBudget.RecipientNoncreate

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

def noncreatePrice (addresses keys : Nat) : Nat :=
  (1999 + WarmPrecompiles.price 19 addresses + 9 * addresses + WarmKeys.price 0 keys +
    GrowRuntime.growthPotential .account (max 64 (4 * (addresses + 21))) +
    GrowRuntime.growthPotential .storage (max 16 (4 * (keys + 1)))) -
    (GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16)

/-- Telescope the final recipient insertion with the preceding complete
warm-up, charging growth only across the actual capacity increases. -/
theorem noncreate_price_bound (first second oldCapacity oldCount nextCapacity nextCount storageCapacity addresses keys : Nat)
    (warm : first + GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16 ≤
      1815 + WarmPrecompiles.price 19 addresses + WarmKeys.price 0 keys + GrowRuntime.growthPotential .account oldCapacity + GrowRuntime.growthPotential .storage storageCapacity)
    (last : second + GrowRuntime.growthPotential .account oldCapacity ≤ Set.noGrowthPrice .account oldCount + 2 + GrowRuntime.growthPotential .account nextCapacity)
    (count : oldCount ≤ 19 + addresses) (next : nextCount ≤ oldCount + 1)
    (oldHigh : oldCapacity ≤ max 64 (4 * (addresses + 20)))
    (newHigh : nextCapacity ≤ max oldCapacity (4 * (nextCount + 1)))
    (storageHigh : storageCapacity ≤ max 16 (4 * (keys + 1))) : first + second ≤ noncreatePrice addresses keys := by
  have accountHigh : nextCapacity ≤ max 64 (4 * (addresses + 21)) := by omega
  have accountPotential := GrowRuntime.potential_mono .account _ _ accountHigh
  have storagePotential := GrowRuntime.potential_mono .storage _ _ storageHigh
  have ordinary := Set.no_growth_caller_price .account oldCount
  change Set.noGrowthPrice .account oldCount + 1 = 9 * oldCount + 12 at ordinary
  have countPrice := Nat.mul_le_mul_left 9 count
  simp only [Nat.mul_add] at countPrice
  unfold noncreatePrice
  omega

/-- The full unchanged non-creation root setup from the actual msg_new
declaration through process_message_call. Input/entry reachability remains
explicit; there is no prospective allocation-room or source-clock premise. -/
theorem noncreate_initialized_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (start txStart addressesStart addressCount keysStart keyCount precompileStart : Nat)
    (blockEnv txEnv : HolWordLab 64) (sender recipient data length gas reservoir : BitVec 64)
    (intrinsicRegular : Nat) (pointers : Nat → BitVec 64) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (record : Recipient.TxData source.memory txStart start recipient data length)
    (precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩)
    (array : PointerArray source.memory 20 addressesStart addressCount start pointers) (positive : 0 < addressCount)
    (keyRegion : MemoryRegion.Valid (WarmKeys.inputRegion keysStart keyCount))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (precompiles : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))))
    (blockGlobal : source.globals.lookup (ofString "be") = some (.val blockEnv))
    (txEnvLocal : source.locals.lookup (ofString "te") = some (.val txEnv))
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart))))
    (gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas)))
    (reservoirLocal : source.locals.lookup (ofString "reservoir") = some (.val (.word reservoir)))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 addressesStart))))
    (countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (addressCount - 1)))))
    (keysLocal : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart))))
    (keyCountLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount))))
    (senderFits : sender.toNat + 20 < 2 ^ 64)
    (senderMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress sender offset)))
    (nonzero : recipient ≠ 0#64) (recipientFits : recipient.toNat + 20 < 2 ^ 64)
    (recipientMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress recipient offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (msgCode : source.code.lookup (ofString "msg_new") = some (MsgNew.formals, MsgNew.body, .one))
    (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (normal : evaluateHOLFiniteState source initialSite = (some (.returned value), post)) :
    ∃ paid accountPlan storagePlan accountSlots storageSlots nextCursor storageStart ready entered warmed final finish,
      paid ≤ source.clock ∧ paid ≤ noncreatePrice addressCount keyCount ∧ final.clock = source.clock - paid ∧
      MemoryRegion.Valid ⟨start, 176⟩ ∧
      TableState final .account accountPlan accountSlots nextCursor (start + 176) ∧ TableState final .storage storagePlan storageSlots nextCursor storageStart ∧
      accountSlots.length ≤ 20 + addressCount ∧ storageSlots.length ≤ keyCount ∧
      final.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) ∧
      final.locals.lookup (ofString "aa") = some (.val (.word (cell accountPlan .header 0))) ∧
      final.locals.lookup (ofString "ak") = some (.val (.word (cell storagePlan .header 0))) ∧
      final.memory (BitVec.ofNat 64 start + 40#64) = .word gas ∧ gas.toNat + intrinsicRegular ≤ 16777216 ∧
      final.memory (BitVec.ofNat 64 start + 152#64) = .word (cell accountPlan .header 0) ∧
      final.memory (BitVec.ofNat 64 start + 160#64) = .word (cell storagePlan .header 0) ∧
      evaluateHOLFiniteState final Recipient.messageSite = (some (.returned value), finish) ∧
      post = restore source "m" (restore ready "aa" (restore entered "ak" (restore warmed "empty" finish))) ∧
      final.code = source.code ∧ WarmKeys.Environment final ∧
      ∀ query : BitVec 64, query.toNat < start → final.memory query = source.memory query := by
  obtain ⟨first, accountPlan, storagePlan, accountSlots, storageSlots, cursor, storageStart, ready, entered, warmed, warmFinish,
    firstFits, firstPrice, firstClock, firstBudget, region, table, reader, separated, count, storageCount, aa, ak, message, gasWord, gasCap,
    warmRun, restored, codes, warmEnvironment, finalArray, accountCapacity, storageCapacity, localFrame, earlierWords⟩ :=
    initialized_normal source post value start addressesStart addressCount keysStart keyCount precompileStart blockEnv txEnv sender gas reservoir intrinsicRegular pointers
      environment lower bounded aligned precompileValid array positive keyRegion heap precompiles blockGlobal txEnvLocal gasLocal reservoirLocal senderLocal
      addressesLocal countLocal keysLocal keyCountLocal senderFits senderMapped newCode msgCode cap normal
  have warmRecord := record.of_protected earlierWords
  have warmTx := (localFrame (ofString "tx") (by decide) (by decide) (by decide) (by decide)).trans txLocal
  have readerLater : ∀ pool, start + 176 ≤ storagePlan.base pool := by
    intro pool
    have accountLower := table.lower .header
    have separation := separated .header pool
    change accountPlan.base .header + 72 ≤ storagePlan.base pool at separation
    omega
  have mapped : ∀ offset < 20, warmed.memaddrs (panByteAlignHOL (width := 64) (byteAddress recipient offset)) := by
    intro offset inside
    rw [warmEnvironment.domain, ← environment.domain]
    exact recipientMapped offset inside
  obtain ⟨second, nextPlan, nextSlots, nextCursor, final, finish, secondFits, secondPrice, secondClock, forward, secondBudget,
    nextTable, nextReader, nextApart, nextLow, nextHigh, nextCapacity, finalMessage, finalAA, finalAK, finalCodes, finalEnvironment,
    finalGas, pointerAA, pointerAK, finalRun, finalRestored, finalProtected⟩ :=
    Recipient.noncreate_normal warmed warmFinish value accountPlan storagePlan accountSlots storageSlots cursor (start + 176) storageStart start txStart
      recipient data length gas warmEnvironment table reader (fun first second => Or.inl (separated first second)) region (Nat.le_refl _) readerLater warmRecord
      message warmTx aa ak gasWord nonzero recipientFits mapped warmRun
  have totalPrice := noncreate_price_bound first second accountPlan.capacity accountSlots.length nextPlan.capacity nextSlots.length storagePlan.capacity addressCount keyCount
    firstBudget secondBudget count nextHigh accountCapacity nextCapacity storageCapacity
  rw [finalRestored] at restored
  refine ⟨first + second, nextPlan, storagePlan, nextSlots, storageSlots, nextCursor, storageStart, ready, entered, warmed, final, finish,
    by omega, totalPrice, by omega, region, nextTable, nextReader, by omega, storageCount, finalMessage, finalAA, finalAK, finalGas, gasCap,
    pointerAA, pointerAK, finalRun, restored, finalCodes.trans codes, finalEnvironment, ?_⟩
  intro query earlier
  exact (finalProtected query earlier).trans (earlierWords query earlier)

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.noncreate_price_bound
#print axioms InitECandidate.Solver.GasBudget.RootMessage.noncreate_initialized_normal

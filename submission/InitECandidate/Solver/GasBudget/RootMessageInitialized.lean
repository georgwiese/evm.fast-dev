import InitECandidate.Solver.GasBudget.RootMessagePrepared
import InitECandidate.Solver.GasBudget.RootMessageWarm

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

/-- Whole actual original root message allocation/initialization and both
warm tables, starting before msg_new. Message geometry, MSG_GAS, all reached
allocation room and both surviving table models are conclusions. -/
theorem initialized_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (start addressesStart addressCount keysStart keyCount precompileStart : Nat)
    (blockEnv txEnv : HolWordLab 64) (sender gas reservoir : BitVec 64) (intrinsicRegular : Nat) (pointers : Nat → BitVec 64)
    (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩)
    (array : PointerArray source.memory 20 addressesStart addressCount start pointers) (positive : 0 < addressCount)
    (keyRegion : MemoryRegion.Valid (WarmKeys.inputRegion keysStart keyCount))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (precompiles : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))))
    (blockGlobal : source.globals.lookup (ofString "be") = some (.val blockEnv))
    (txLocal : source.locals.lookup (ofString "te") = some (.val txEnv))
    (gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas)))
    (reservoirLocal : source.locals.lookup (ofString "reservoir") = some (.val (.word reservoir)))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 addressesStart))))
    (countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (addressCount - 1)))))
    (keysLocal : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart))))
    (keyCountLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount))))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (msgCode : source.code.lookup (ofString "msg_new") = some (MsgNew.formals, MsgNew.body, .one))
    (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (normal : evaluateHOLFiniteState source initialSite = (some (.returned value), post)) :
    ∃ paid accountPlan storagePlan accountSlots storageSlots nextCursor storageStart ready entered warmed finish,
      paid ≤ source.clock ∧ paid ≤ 10 + WarmTables.price addressCount keyCount ∧ warmed.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account 64 + GrowRuntime.growthPotential .storage 16 ≤
        1815 + WarmPrecompiles.price 19 addressCount + WarmKeys.price 0 keyCount + GrowRuntime.growthPotential .account accountPlan.capacity + GrowRuntime.growthPotential .storage storagePlan.capacity ∧
      MemoryRegion.Valid ⟨start, 176⟩ ∧
      TableState warmed .account accountPlan accountSlots nextCursor (start + 176) ∧ TableState warmed .storage storagePlan storageSlots nextCursor storageStart ∧
      (∀ first second, accountPlan.base first + size .account accountPlan first ≤ storagePlan.base second) ∧
      accountSlots.length ≤ 19 + addressCount ∧ storageSlots.length ≤ keyCount ∧
      warmed.locals.lookup (ofString "aa") = some (.val (.word (cell accountPlan .header 0))) ∧
      warmed.locals.lookup (ofString "ak") = some (.val (.word (cell storagePlan .header 0))) ∧
      warmed.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) ∧
      warmed.memory (BitVec.ofNat 64 start + 40#64) = .word gas ∧
      warmed.memory (BitVec.ofNat 64 start + 48#64) = .word reservoir ∧ gas.toNat + intrinsicRegular ≤ 16777216 ∧
      evaluateHOLFiniteState warmed WarmKeys.afterLoop = (some (.returned value), finish) ∧
      post = restore source "m" (restore ready "aa" (restore entered "ak" finish)) ∧ warmed.code = source.code ∧ WarmKeys.Environment warmed ∧
      PointerArray warmed.memory 20 addressesStart addressCount start pointers ∧
      accountPlan.capacity ≤ max 64 (4 * (addressCount + 20)) ∧ storagePlan.capacity ≤ max 16 (4 * (keyCount + 1)) ∧
      (∀ key : MlS, key ≠ ofString "m" → key ≠ ofString "aa" → key ≠ ofString "ak" → key ≠ ofString "i" → warmed.locals.lookup key = source.locals.lookup key) ∧
      ∀ query : BitVec 64, query.toNat < start → warmed.memory query = source.memory query := by
  obtain ⟨stored, inner, prepared, storedRun, sourceRestored⟩ := allocation_normal source post value start blockEnv txEnv sender gas lower bounded aligned environment.domain heap
    blockGlobal txLocal senderLocal gasLocal environment.allocCode environment.trapCode environment.zeroCode msgCode normal
  have codes := congrArg PanSemStateFiniteExact.code prepared.frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs prepared.frame
  have endian := congrArg PanSemStateFiniteExact.be prepared.frame
  have clock := congrArg PanSemStateFiniteExact.clock prepared.frame
  change stored.code = source.code at codes
  change stored.memaddrs = source.memaddrs at domain
  change stored.be = source.be at endian
  change stored.clock = source.clock - 10 at clock
  have storedEnvironment : WarmKeys.Environment stored := environment.of_fields codes domain endian
  have localWord (name : String) (word : BitVec 64) (different : ofString "m" ≠ ofString name)
      (read : source.locals.lookup (ofString name) = some (.val (.word word))) : stored.locals.lookup (ofString name) = some (.val (.word word)) := by
    rw [prepared.frame]
    exact (bind_lookup_other _ "m" name _ different).trans read
  have storedHeap : stored.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 176)))) := by
    rw [prepared.frame]
    simp [MsgNew.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have storedPrecompiles : stored.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))) := by rw [prepared.frame]; exact precompiles
  have storedMessage : stored.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [prepared.frame]; exact bind_lookup_same _ _ _
  have storedArray := array.of_protected (fun query before => prepared.outside query (Or.inl before))
  have constructorCode : stored.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one) := by rw [codes]; exact newCode
  have mapped : ∀ offset < 20, stored.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)) := by intro offset inside; rw [domain]; exact queryMapped offset inside
  have nextAligned : (start + 176) % 8 = 0 := by omega
  obtain ⟨paid, accountPlan, storagePlan, accountSlots, storageSlots, nextCursor, storageStart, ready, entered, warmed, finish,
    fits, price, spent, budget, accountTable, storageTable, separated, accountCount, storageCount, finalAccount, finalStorage, finalMessage, finalGas, finalReservoir, finalCap, restRun, restored, finalCodes, finalEnvironment, finalArray,
    accountCapacity, storageCapacity, finalLocalFrame, finalProtected⟩ :=
    warm_normal stored inner value start (start + 176) addressesStart addressCount keysStart keyCount precompileStart sender gas reservoir intrinsicRegular pointers storedEnvironment
      prepared.region (Nat.le_refl _) prepared.region.upper nextAligned precompileValid storedArray positive keyRegion storedHeap storedPrecompiles storedMessage
      (localWord "reservoir" _ (by decide) reservoirLocal) (localWord "sender" _ (by decide) senderLocal)
      (localWord "al_addrs" _ (by decide) addressesLocal) (localWord "nal" _ (by decide) countLocal)
      (localWord "al_keys" _ (by decide) keysLocal) (localWord "nkeys" _ (by decide) keyCountLocal) queryFits mapped constructorCode prepared.gas cap storedRun
  have earlierWords : ∀ query : BitVec 64, query.toNat < start → warmed.memory query = source.memory query := by
    intro query before
    exact (finalProtected query before).trans (prepared.outside query (Or.inl before))
  have funded := prepared.funded
  refine ⟨10 + paid, accountPlan, storagePlan, accountSlots, storageSlots, nextCursor, storageStart, ready, entered, warmed, finish,
    by omega, by omega, by omega, by omega, prepared.region, accountTable, storageTable, separated, accountCount, storageCount, finalAccount, finalStorage, finalMessage, finalGas, finalReservoir, finalCap,
    restRun, ?_, finalCodes.trans codes, finalEnvironment, array.of_protected earlierWords, accountCapacity, storageCapacity, ?_, earlierWords⟩
  · rw [restored] at sourceRestored
    exact sourceRestored
  · intro key notMessage notAccount notStorage notIndex
    rw [finalLocalFrame key notAccount notStorage notIndex, prepared.frame]
    simp [MsgNew.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notMessage, Ne.symm notMessage]

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.initialized_normal

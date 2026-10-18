import InitECandidate.Solver.GasBudget.RootMessageStores
import InitECandidate.Solver.GasBudget.WarmTables

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Actual post-MSG_GAS transaction continuation through both remaining
message stores and every warm-table constructor/mutation. The physical gas
word, message binding and complete two-table model survive this whole phase. -/
theorem warm_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (messageStart cursor addressesStart addressCount keysStart keyCount precompileStart : Nat)
    (sender gas reservoir : BitVec 64) (intrinsicRegular : Nat) (pointers : Nat → BitVec 64)
    (environment : WarmKeys.Environment source)
    (region : MemoryRegion.Valid ⟨messageStart, 176⟩) (messageBefore : messageStart + 176 ≤ cursor)
    (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩)
    (array : PointerArray source.memory 20 addressesStart addressCount messageStart pointers) (positive : 0 < addressCount)
    (keyRegion : MemoryRegion.Valid (WarmKeys.inputRegion keysStart keyCount))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (precompiles : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))))
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))))
    (reservoirLocal : source.locals.lookup (ofString "reservoir") = some (.val (.word reservoir)))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 addressesStart))))
    (countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (addressCount - 1)))))
    (keysLocal : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart))))
    (keyCountLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount))))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one))
    (gasCell : source.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas)
    (cap : gas.toNat + intrinsicRegular ≤ 16777216)
    (normal : evaluateHOLFiniteState source RootCaller.afterMsgGas = (some (.returned value), post)) :
    ∃ paid accountPlan storagePlan accountSlots storageSlots nextCursor storageStart ready entered warmed finish,
      paid ≤ source.clock ∧ paid ≤ WarmTables.price addressCount keyCount ∧ warmed.clock = source.clock - paid ∧
      TableState warmed .account accountPlan accountSlots nextCursor cursor ∧ TableState warmed .storage storagePlan storageSlots nextCursor storageStart ∧
      (∀ first second, accountPlan.base first + size .account accountPlan first ≤ storagePlan.base second) ∧
      accountSlots.length ≤ 19 + addressCount ∧ storageSlots.length ≤ keyCount ∧
      warmed.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))) ∧
      warmed.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas ∧ gas.toNat + intrinsicRegular ≤ 16777216 ∧
      evaluateHOLFiniteState warmed WarmKeys.afterLoop = (some (.returned value), finish) ∧
      post = restore ready "aa" (restore entered "ak" finish) ∧ warmed.code = source.code ∧ WarmKeys.Environment warmed ∧
      PointerArray warmed.memory 20 addressesStart addressCount messageStart pointers ∧
      ∀ query : BitVec 64, query.toNat < messageStart → warmed.memory query = source.memory query := by
  obtain ⟨ready, readyRun, readyFrame, readyGas, readyOutside⟩ := stores_normal source post value messageStart reservoir region messageLocal reservoirLocal normal
  have locals := congrArg PanSemStateFiniteExact.locals readyFrame
  have globals := congrArg PanSemStateFiniteExact.globals readyFrame
  have codes := congrArg PanSemStateFiniteExact.code readyFrame
  have domain := congrArg PanSemStateFiniteExact.memaddrs readyFrame
  have endian := congrArg PanSemStateFiniteExact.be readyFrame
  have clock := congrArg PanSemStateFiniteExact.clock readyFrame
  change ready.locals = source.locals at locals
  change ready.globals = source.globals at globals
  change ready.code = source.code at codes
  change ready.memaddrs = source.memaddrs at domain
  change ready.be = source.be at endian
  change ready.clock = source.clock at clock
  have readyEnvironment : WarmKeys.Environment ready := environment.of_fields codes domain endian
  have protectedArray := array.of_protected (fun query before => readyOutside query (Or.inl before))
  have readyArray := protectedArray.floor_mono cursor (by omega)
  have localWord (name : MlS) (word : BitVec 64) (read : source.locals.lookup name = some (.val (.word word))) : ready.locals.lookup name = some (.val (.word word)) := by rw [locals]; exact read
  have globalWord (name : MlS) (word : BitVec 64) (read : source.globals.lookup name = some (.val (.word word))) : ready.globals.lookup name = some (.val (.word word)) := by rw [globals]; exact read
  have code : ready.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one) := by rw [codes]; exact newCode
  have mapped : ∀ offset < 20, ready.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)) := by intro offset inside; rw [domain]; exact queryMapped offset inside
  obtain ⟨paid, accountPlan, storagePlan, accountSlots, storageSlots, nextCursor, storageStart, entered, warmed, finish,
    fits, price, spent, budget, accountTable, storageTable, separated, accountCount, storageCount, accountCapacity, storageCapacity, accountLocal, storageLocals, finalEnvironment,
    restRun, restored, finalCodes, finalArray, finalProtected, finalLocalFrame⟩ :=
    WarmTables.normal_bound ready post value cursor addressesStart addressCount keysStart keyCount sender pointers readyEnvironment
      (by have lower := region.lower; change 2701131776 ≤ messageStart at lower; omega) cursorBound cursorAligned precompileStart precompileValid readyArray positive keyRegion
      (globalWord _ _ heap) (globalWord _ _ precompiles) (localWord _ _ senderLocal) (localWord _ _ addressesLocal) (localWord _ _ countLocal)
      (localWord _ _ keysLocal) (localWord _ _ keyCountLocal) queryFits mapped code readyRun
  have gasBefore : (BitVec.ofNat 64 messageStart + 40#64).toNat < cursor := by
    have number := MessageField.field_number messageStart 40 region (by decide)
    change (BitVec.ofNat 64 messageStart + 40#64).toNat = messageStart + 40 at number
    omega
  have earlierWords : ∀ query : BitVec 64, query.toNat < messageStart → warmed.memory query = source.memory query := by
    intro query before
    exact (finalProtected query (by omega)).trans (readyOutside query (Or.inl before))
  refine ⟨paid, accountPlan, storagePlan, accountSlots, storageSlots, nextCursor, storageStart, ready, entered, warmed, finish,
    by omega, price, by omega, accountTable, storageTable, separated, accountCount, storageCount, ?_, ?_, cap, restRun, restored, finalCodes.trans codes, finalEnvironment, array.of_protected earlierWords, earlierWords⟩
  · exact (finalLocalFrame _ (by decide) (by decide) (by decide)).trans (localWord _ _ messageLocal)
  · exact (finalProtected _ gasBefore).trans (readyGas.trans gasCell)

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.warm_normal

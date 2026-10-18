import InitECandidate.Solver.GasBudget.WarmAddressesLoop
import InitECandidate.Solver.GasBudget.WarmPrecompilesConstructor

namespace InitECandidate.Solver.GasBudget.WarmAccounts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Actual original account warm-up prewarmed: constructor, sender, 18
precompiles, coinbase and all access-list addresses. Every address-array
read, mutation, reached growth and cursor/model transition is accounted for. -/
theorem normal_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (cursor start count : Nat) (sender : BitVec 64) (pointers : Nat → BitVec 64) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ cursor) (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (precompileStart : Nat) (precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩)
    (array : PointerArray source.memory 20 start count cursor pointers) (positive : 0 < count)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (keys : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart))))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 start))))
    (countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (count - 1)))))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one))
    (normal : evaluateHOLFiniteState source WarmPrecompiles.constructorSite = (some (.returned value), post)) :
    ∃ paid plan slots nextCursor warmed finish,
      paid ≤ source.clock ∧ warmed.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account 64 ≤ 1795 + WarmPrecompiles.price 19 count + GrowRuntime.growthPotential .account plan.capacity ∧
      TableState warmed .account plan slots nextCursor cursor ∧ WarmKeys.Environment warmed ∧
      PointerArray warmed.memory 20 start count cursor pointers ∧
      WarmAddresses.Locals warmed (cell plan .header 0) start count count ∧ slots.length ≤ 19 + count ∧
      plan.capacity ≤ max 64 (4 * (count + 20)) ∧
      evaluateHOLFiniteState warmed WarmAddresses.afterLoop = (some (.returned value), finish) ∧ post = restore source "aa" finish ∧ warmed.code = source.code ∧
      HeapGlobals source warmed ∧
      (∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address) ∧
      ∀ key : MlS, key ≠ ofString "aa" → key ≠ ofString "i" → warmed.locals.lookup key = source.locals.lookup key := by
  obtain ⟨prefixPaid, prefixSlots, prewarmed, inner, prefixBound, prefixFits, prefixClock, prefixFrame, prefixHeader, prefixModel, prefixCount, prefixLocals,
    prefixRun, restored, prefixProtected, prefixLocalFrame⟩ :=
    WarmPrecompiles.constructor_normal source post value cursor precompileStart sender environment lower bounded aligned precompileValid heap keys senderLocal queryFits queryMapped newCode normal
  have actual := normal
  rw [WarmPrecompiles.constructor_shape] at actual
  have valid := TableRuntime.normal_call_layout source post .account cursor 64 "aa" WarmPrecompiles.newArguments WarmPrecompiles.afterNew
    (by decide) lower bounded aligned (by decide) (by decide) (by decide) (by decide) environment.domain rfl newCode heap
    environment.allocCode environment.trapCode environment.zeroCode value actual
  let initialPlan := fresh .account cursor 64
  let initialCursor := freshEnd .account cursor 64
  have cursorBound : initialCursor ≤ 33806089496 := valid.upper .position
  have cursorAligned : initialCursor % 8 = 0 := by simpa [initialCursor, freshEnd, stride, KeyHash.keySize, rounded, Nat.add_mod] using aligned
  have globals := congrArg PanSemStateFiniteExact.globals prefixFrame
  have codes := congrArg PanSemStateFiniteExact.code prefixFrame
  have domain := congrArg PanSemStateFiniteExact.memaddrs prefixFrame
  have endian := congrArg PanSemStateFiniteExact.be prefixFrame
  change prewarmed.globals = (TableRuntime.callState source "aa" .account cursor 64).globals at globals
  change prewarmed.code = source.code at codes
  change prewarmed.memaddrs = source.memaddrs at domain
  change prewarmed.be = source.be at endian
  have prefixHeap : prewarmed.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 initialCursor))) := by
    rw [globals]
    simp [TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, initialCursor]
  have prefixTable : TableState prewarmed .account initialPlan prefixSlots initialCursor cursor :=
    ⟨valid, by change 2 * prefixSlots.length ≤ 64; omega, prefixHeader, prefixModel, ⟨6, rfl, by decide⟩,
      prefixHeap, cursorBound, cursorAligned, fun pool => (fresh_bounds .account cursor 64 pool).2, fun pool => (fresh_bounds .account cursor 64 pool).1⟩
  have prefixEnvironment : WarmKeys.Environment prewarmed := environment.of_fields codes domain endian
  have prefixArray := array.of_protected prefixProtected
  rw [WarmAddresses.entry_shape] at prefixRun
  have resetSafe : Input.LocalPrefix (ofString "m") WarmAddresses.resetIndex := .assign _ _ (by decide)
  obtain ⟨reset, resetRun, siteRun, _⟩ := resetSafe.normal_continue prewarmed inner WarmAddresses.site value prefixRun
  have resetEq := Input.assign_none prewarmed reset "i" (.const 0#64) 0#64 rfl resetRun
  let ready := bind prewarmed "i" 0#64
  change reset = ready at resetEq
  subst reset
  have readyLocals : WarmAddresses.Locals ready (cell initialPlan .header 0) start count 0 := by
    refine ⟨(bind_lookup_other _ "i" "aa" _ (by decide)).trans prefixLocals.table, ?_, ?_, bind_lookup_same _ _ _⟩
    · rw [bind_lookup_other _ "i" "al_addrs" _ (by decide), prefixLocalFrame _ (by decide) (by decide)]
      exact addressesLocal
    · rw [bind_lookup_other _ "i" "nal" _ (by decide), prefixLocalFrame _ (by decide) (by decide)]
      exact countLocal
  rw [WarmAddresses.site_shape] at siteRun
  have loopSafe : Input.LocalPrefix (ofString "m") WarmAddresses.loop := .loop _ WarmAddresses.body_safe
  obtain ⟨warmed, loopRun, restRun, _⟩ := loopSafe.normal_continue ready inner WarmAddresses.afterLoop value siteRun
  have readyTable : TableState ready .account initialPlan prefixSlots initialCursor cursor := prefixTable.of_fields rfl rfl rfl rfl
  have readyEnvironment : WarmKeys.Environment ready := prefixEnvironment.of_fields rfl rfl rfl
  obtain ⟨loopPaid, plan, slots, nextCursor, loopFits, loopClock, loopBound, finalTable, finalEnvironment, finalArray, finalLocals, finalLower, finalUpper, finalCapacity, finalGlobals, finalProtected⟩ :=
    WarmAddresses.loop_normal count ready warmed start count 0 cursor initialCursor initialPlan prefixSlots pointers prefixArray positive (by omega) readyEnvironment readyTable readyLocals loopRun
  have priced := WarmPrecompiles.price_mono prefixSlots.length 19 count prefixCount
  change loopPaid + GrowRuntime.growthPotential .account 64 ≤ WarmPrecompiles.price prefixSlots.length count + GrowRuntime.growthPotential .account plan.capacity at loopBound
  change loopPaid ≤ prewarmed.clock at loopFits
  change warmed.clock = prewarmed.clock - loopPaid at loopClock
  change plan.capacity ≤ max 64 (4 * (prefixSlots.length + count + 1)) at finalCapacity
  have initialGlobals : HeapGlobals source ready := by
    intro key different
    change prewarmed.globals.lookup key = source.globals.lookup key
    rw [globals]
    simp [TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]
  refine ⟨prefixPaid + loopPaid, plan, slots, nextCursor, warmed, inner, by omega, by omega, by omega,
    finalTable, finalEnvironment, finalArray, finalLocals, by omega, by omega, restRun, restored, ?_, initialGlobals.trans finalGlobals, ?_, ?_⟩
  · have fields := Input.evaluation_fields ready warmed WarmAddresses.loop none loopRun
    exact fields.2.2.2.trans codes
  · intro address before
    exact (finalProtected address before).trans (prefixProtected address before)
  · intro key notTable notIndex
    have same := Input.counter_loop_local ready warmed WarmAddresses.condition (ofString "htab_set")
      [localVar "aa", WarmAddresses.query, .const 1#64] "i" (.op .add [localVar "i", .const 1#64]) key notIndex loopRun
    calc
      warmed.locals.lookup key = ready.locals.lookup key := same
      _ = prewarmed.locals.lookup key := by simp [ready, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notIndex, Ne.symm notIndex]
      _ = source.locals.lookup key := prefixLocalFrame key notTable notIndex

end InitECandidate.Solver.GasBudget.WarmAccounts

#print axioms InitECandidate.Solver.GasBudget.WarmAccounts.normal_bound

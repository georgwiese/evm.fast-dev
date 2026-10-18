import InitECandidate.Solver.GasBudget.RootActiveEntry

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

/-- Whole actual non-creation root setup and active-child initialization.
Both original warm tables survive output and arena allocations. Input/code/
arena entry reachability remains explicit; no numerical score gate, helper
execution, intermediate model or source-clock allowance is assumed. -/
theorem active_noncreate_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (setup : NoncreateSetup source) (frameCode : FrameCode source) (arena : ArenaEntry source setup.start)
    (normal : evaluateHOLFiniteState source initialSite = (some (.returned value), post)) :
    ∃ (paid cursor storageFloor : Nat) (account storage : Plan) (accountSlots storageSlots : List Nat)
      (active : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ paid ≤ noncreatePrice setup.addressCount setup.keyCount + 53 ∧ active.clock = source.clock - paid ∧
      TableState active .account account accountSlots cursor (setup.start + 176) ∧ TableState active .storage storage storageSlots cursor storageFloor ∧
      accountSlots.length ≤ 20 + setup.addressCount ∧ storageSlots.length ≤ setup.keyCount ∧
      regularBudget active.memory (FrameNew.framePointer arena.scratch) = setup.gas.toNat ∧
      regularBudget active.memory (FrameNew.framePointer arena.scratch) + setup.intrinsicRegular ≤ 16777216 ∧
      active.globals.lookup (ofString "ev") = some (.val (.word (FrameNew.framePointer arena.scratch))) ∧
      active.globals.lookup (ofString "cur_cont") = some (.val (.word (FrameOpen.recordPointer (FrameNew.finalScratch arena.scratch 0#64)))) ∧
      active.code = source.code ∧ WarmKeys.Environment active ∧
      evaluateHOLFiniteState active ProcessMessage.afterOpen = (some (.returned returned), finish) := by
  obtain ⟨setupPaid, account, storage, accountSlots, storageSlots, cursor, storageFloor, emptyStart, ready, entered, warmed, callSource, callPost,
    setupFits, setupPrice, setupClock, region, accountTable, storageTable, storageLater, accountCount, storageCount,
    messageLocal, aaLocal, akLocal, gasCell, gasCap, reservoirCell, codeCell, lengthCell, recipientCell, accountCell, storageCell,
    callRun, restored, codes, environment, globals, protectedWords⟩ :=
    noncreate_initialized_normal source post value setup.start setup.txStart setup.addressesStart setup.addressCount setup.keysStart setup.keyCount setup.precompileStart
      setup.blockEnv setup.txEnv setup.sender setup.recipient setup.data setup.length setup.gas setup.reservoir setup.intrinsicRegular setup.pointers setup.environment
      setup.lower setup.bounded setup.aligned setup.record setup.precompileValid setup.array setup.positive setup.keyRegion setup.heap setup.precompiles
      setup.blockGlobal setup.txEnvLocal setup.txLocal setup.gasLocal setup.reservoirLocal setup.senderLocal setup.addressesLocal setup.countLocal setup.keysLocal setup.keyCountLocal
      setup.senderFits setup.senderMapped setup.nonzero setup.recipientFits setup.recipientMapped setup.newCode setup.msgCode setup.cap normal
  have finalCode : FrameCode callSource := frameCode.of_code codes
  have globalWord (name : String) (word : BitVec 64) (different : ofString name ≠ ofString "heap_ptr")
      (read : source.globals.lookup (ofString name) = some (.val (.word word))) : callSource.globals.lookup (ofString name) = some (.val (.word word)) :=
    (globals (ofString name) different).trans read
  have accountLater : setup.start + 176 ≤ account.base .header := accountTable.lower .header
  have entry := FrameNew.empty_message_entry callSource arena.scratch arena.lower arena.empty (BitVec.ofNat 64 emptyStart) setup.gas setup.reservoir
    setup.start cursor (setup.start + 176) storageFloor account storage accountSlots storageSlots environment.domain finalCode.prefixCode finalCode.memoryCode
    finalCode.jumpCode finalCode.logCode finalCode.tableCode finalCode.countCode
    (globalWord "scratch_ptr" _ (by decide) arena.scratchGlobal) (globalWord "frame_mem_ptr" _ (by decide) arena.lowerGlobal)
    (globalWord "evm_empty" _ (by decide) arena.emptyGlobal) arena.scratchAligned arena.lowerAligned arena.lowerBound arena.scratchBound
    (by have room := arena.room; omega) region arena.persistent accountTable storageTable accountLater (storageLater .header)
    codeCell lengthCell gasCell reservoirCell accountCell storageCell
  have cursorLower : 2701131776 ≤ cursor := by
    have lower := accountTable.valid.lower .header
    have earlier := accountTable.earlier .header
    change account.base .header + 72 ≤ cursor at earlier
    omega
  have messageBefore : setup.start + 176 ≤ cursor := by
    have earlier := accountTable.earlier .header
    change account.base .header + 72 ≤ cursor at earlier
    omega
  have headerBefore (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (floor : Nat)
      (table : TableState callSource kind plan slots cursor floor) : (cell plan .header 0).toNat + 32 ≤ cursor := by
    rw [base_number kind plan table.valid .header]
    have earlier := table.earlier .header
    change plan.base .header + 72 ≤ cursor at earlier
    omega
  have room : arena.lower.toNat + JumpDest.bitmapBytes (0#64 : BitVec 64).toNat + 2760 ≤ arena.scratch.toNat := by
    simpa [JumpDest.bitmapBytes] using arena.room
  obtain ⟨callPaid, active, returned, finish, callFits, callPrice, callClock, budget, activeCap, activeGlobal, activeContinuation,
    activeCodes, activeHeap, activeBound, activeDomain, activeEndian, afterOpenRun, earlierMemory⟩ :=
    MessageCall.call_open_normal callSource callPost value setup.start cursor arena.scratch arena.lower arena.empty arena.parent arena.continuation setup.recipient setup.gas setup.intrinsicRegular
      ⟨BitVec.ofNat 64 emptyStart, 0#64, setup.gas, setup.reservoir⟩ (cell account .header 0) (cell storage .header 0) (BitVec.ofNat 64 accountSlots.length) (BitVec.ofNat 64 storageSlots.length)
      entry environment cursorLower accountTable.bounded accountTable.aligned accountTable.heap region messageBefore
      (headerBefore .account account accountSlots (setup.start + 176) accountTable) (headerBefore .storage storage storageSlots storageFloor storageTable)
      messageLocal recipientCell setup.nonzero gasCell gasCap finalCode.callCode finalCode.messageCode finalCode.openCode finalCode.newCode
      (globalWord "ev" _ (by decide) arena.evGlobal) (globalWord "cur_cont" _ (by decide) arena.continuationGlobal) room callRun
  change callPaid ≤ (0#64 : BitVec 64).toNat + Zero.price (JumpDest.bitmapBytes (0#64 : BitVec 64).toNat) + 52 at callPrice
  rw [empty_activation_price] at callPrice
  have activeTable (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (floor : Nat)
      (table : TableState callSource kind plan slots cursor floor) (later : ∀ pool, arena.scratch.toNat ≤ plan.base pool) :
      TableState active kind plan slots (cursor + 96) floor := by
    have pools : MemoryModel.PoolFrame callSource.memory active.memory kind plan := by
      intro pool offset inside
      have number := NaturalLayout.number kind plan table.valid pool offset inside
      apply earlierMemory
      · right
        rw [number]
        have lower := later pool
        omega
      · rw [number]
        have earlier := table.earlier pool
        omega
    exact ⟨table.valid, table.half, MemoryModel.Header.of_pool_frame _ _ kind plan _ table.header pools,
      MemoryModel.Occupied.of_pool_frame callSource active kind plan table.valid slots table.occupied activeDomain activeEndian pools,
      table.power, activeHeap, activeBound, by have aligned := table.aligned; omega,
      (by intro pool; have earlier := table.earlier pool; omega), table.lower⟩
  have nextAccount := activeTable .account account accountSlots (setup.start + 176) accountTable
    (by intro pool; have lower := accountTable.lower pool; have persistent := arena.persistent; omega)
  have nextStorage := activeTable .storage storage storageSlots storageFloor storageTable
    (by intro pool; have lower := storageLater pool; have persistent := arena.persistent; omega)
  have activeEnvironment : WarmKeys.Environment active := environment.of_fields activeCodes activeDomain activeEndian
  refine ⟨setupPaid + callPaid, cursor + 96, storageFloor, account, storage, accountSlots, storageSlots, active, returned, finish,
    by omega, by omega, by omega, nextAccount, nextStorage, accountCount, storageCount, budget, activeCap,
    activeGlobal, activeContinuation, activeCodes.trans codes, activeEnvironment, afterOpenRun⟩

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.active_noncreate_normal

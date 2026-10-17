import InitECandidate.Solver.MutableTable.WitnessBuildRadixPopulateSupported
import InitECandidate.Solver.MutableTable.WitnessBuildPreparedAgreement
import InitECandidate.Solver.MutableTable.WitnessBuildPopulate
import InitECandidate.Solver.WitnessRadix.ConstructorTablePopulate

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Each program preserves earlier safe words through actual allocation,
clearing, array setup, record hashing,
dictionary/radix construction and both returns/scopes from actual entry facts.
The resulting private maps implement the same observed ordinal dictionary. -/
theorem paired_table_populate_supported (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (bits maximum : Nat) (smallBits : bits < 64) (power : plan.capacity = 2^bits)
    (shape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (leftTableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (rightTableCode : right.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (leftAllocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (rightAllocCode : right.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (recordsLocal : source.locals.lookup (ofString "slice_arr") = some (.val (.word (BitVec.ofNat 64 plan.records))))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))))
    (records : Records source plan (fun i => sliceFor (BitVec.ofNat 64 i)))
    (leftContext : Context source plan (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightEnvironment : Keccak256.Environment right stp pad)
    (rightHashCode : right.code.lookup (ofString "keccak256") = some (Keccak256.formals, Keccak256.body, .one))
    (helperCode : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (locals : source.locals = right.locals) (globals : source.globals = right.globals)
    (endian : source.be = right.be) (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (same : MemoryRegion.Agree region source.memory right.memory)
    (before : ∀ query, region query → query.toNat < plan.table)
    (recordPublic : ∀ i < plan.count,
      region (BackingLayout.cell (AllocatedLayout.layout plan) .records (16*i)) ∧
      region (BackingLayout.cell (AllocatedLayout.layout plan) .records (16*i+8)))
    (buffers : ∀ i < plan.count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (safe : BitVec 64 → Prop)
    (safeBefore : ∀ query,safe query → query.toNat<plan.table)
    (safeProtected : ∀ query,safe query → Keccak256.Protected stp pad scratch query)
    (leftClock : tablePopulatePrice maximum plan ≤ source.clock)
    (rightClock : Constructor.tablePopulatePrice maximum plan ≤ right.clock) :
    ∃ finalCount input logical keyFor leftTarget rightTarget root,
      evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new")
        [.const 32#64, localVar "cap"] tableTail) =
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), leftTarget) ∧
      evaluateHOLFiniteState right (.decCall (ofString "t") .one (ofString "htab_new")
        [.const 32#64, localVar "cap"] Constructor.tableTail) =
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), rightTarget) ∧
      Layout32.Built bits leftTarget plan scratch finalCount input logical ∧ History plan input ∧
      KeysMatch plan keyFor input ∧ input.length = plan.count ∧ Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      rightTarget.memaddrs (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) ∧
      rightTarget.memory (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) = .word root ∧
      QueryMemory.Represents rightTarget (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
        (AllocatedLayout.layout plan).vals root
        (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals plan.count)) ∧
      KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl (prepared source plan) ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl (Constructor.preparedState right plan) ∧
      leftTarget.clock ≤ source.clock ∧ source.clock - tablePopulatePrice maximum plan ≤ leftTarget.clock ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - Constructor.tablePopulatePrice maximum plan ≤ rightTarget.clock ∧
      leftTarget.globals = rightTarget.globals ∧ leftTarget.ffi = rightTarget.ffi ∧
      MemoryRegion.Agree region leftTarget.memory rightTarget.memory ∧
      (∀ query,safe query → leftTarget.memory query=source.memory query) ∧
      (∀ query,safe query → rightTarget.memory query=right.memory query) ∧
      (∀ query,QueryMemory.reads rightTarget (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
        (AllocatedLayout.layout plan).vals root (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals plan.count)) query →
        BackingLayout.Protected (AllocatedLayout.layout plan) plan.count query) := by
  classical
  have rightCap : right.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))) := by rw [← locals]; exact capLocal
  have rightHeap : right.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))) := by rw [← globals]; exact heap
  have rightRecords : right.locals.lookup (ofString "slice_arr") = some (.val (.word (BitVec.ofNat 64 plan.records))) := by rw [← locals]; exact recordsLocal
  have rightCount : right.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))) := by rw [← locals]; exact countLocal
  have rightGlobal : right.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word scratch)) := by rw [← globals]; exact leftContext.global
  have rightLittle := endian.symm.trans leftContext.little
  have pointers : ∀ i < plan.count, right.memory (BackingLayout.cell (AllocatedLayout.layout plan) .records (16*i)) =
      .word (sliceFor (BitVec.ofNat 64 i)).1 := by
    intro i inside
    have word := records.pointers i inside
    simp only [record_backing, Nat.add_zero] at word
    exact (same _ (recordPublic i inside).1).symm.trans word
  have lengths : ∀ i < plan.count, right.memory (BackingLayout.cell (AllocatedLayout.layout plan) .records (16*i+8)) =
      .word (sliceFor (BitVec.ofNat 64 i)).2 := by
    intro i inside
    have word := records.lengths i inside
    rw [record_backing] at word
    exact (same _ (recordPublic i inside).2).symm.trans word
  obtain ⟨leftBuilt, leftLocals, leftRecords, leftEntryClock⟩ := prepare_data source plan ready leftContext.environment.domain
    shape leftContext.little bits scratch recordsLocal countLocal _ records
  obtain ⟨rightFixed, rightMapped, rightPrefix, rightLocals, rightN, rightT, rightEntryClock⟩ :=
    Constructor.prepare_data right plan ready rightEnvironment.domain (fun _ _ => 0#8) sliceFor rightRecords rightCount pointers lengths
  have leftPreparedContext := prepared_context source plan _ stp pad scratch maximum leftContext
  have rightPreparedContext := Constructor.prepared_hash_context right plan ready sliceFor stp pad scratch maximum rightEnvironment
    rightGlobal rightHashCode leftContext.buffers leftContext.before leftContext.aligned rightLittle leftContext.lengthBound
  obtain ⟨preparedMemory, preparedFfi, preparedGlobals⟩ := prepared_agrees source right plan ready region before same ffi globals
  obtain ⟨finalCount, input, logical, keyFor, leftFilled, rightFilled, root, leftFilledRun, rightFilledRun,
    filledBuilt, filledHistory, filledMatching, filledLength, filledRecords, filledRootMapped, filledRootWord, filledRep,
    leftControl, rightControl, leftUpper, leftLower, rightUpper, rightLower, filledFfi, filledMemory,leftSaved,rightSaved,filledSupport⟩ :=
    paired_populate_supported (prepared source plan) (Constructor.preparedState right plan) plan ready bits maximum smallBits power sliceFor stp pad scratch
      leftBuilt leftLocals leftRecords rightMapped rightLocals rightN rightT rightFixed leftPreparedContext rightPreparedContext helperCode
      preparedFfi region preparedMemory buffers before safe safeBefore safeProtected
      (by rw [leftEntryClock]; unfold tablePopulatePrice at leftClock; omega)
      (by rw [rightEntryClock]; unfold Constructor.tablePopulatePrice at rightClock; omega)
  have leftPrepare := prepare_execute source plan ready leftContext.environment.domain shape capLocal heap leftTableCode leftAllocCode
    leftContext.environment.zeroCode (by unfold tablePopulatePrice at leftClock; omega)
  obtain ⟨restoreStack, restoreFrame, rightPrepare⟩ := Constructor.prepare_execute_framed right plan ready rightEnvironment.domain shape
    rightCap rightHeap rightTableCode rightAllocCode rightEnvironment.zeroCode
    (by unfold Constructor.tablePopulatePrice at rightClock; omega)
  let leftTarget := finishScope source plan leftFilled
  let rightTarget := restore right "t" (restoreStack rightFilled)
  have rightFrame : emptyLocalsHOLFinite rightTarget = emptyLocalsHOLFinite rightFilled := restoreFrame rightFilled
  have rightMemory : rightTarget.memory = rightFilled.memory := congrArg (fun state => state.memory) rightFrame
  have rightDomain : rightTarget.memaddrs = rightFilled.memaddrs := congrArg (fun state => state.memaddrs) rightFrame
  have rightEndian : rightTarget.be = rightFilled.be := congrArg (fun state => state.be) rightFrame
  have rightFfi : rightTarget.ffi = rightFilled.ffi := congrArg (fun state => state.ffi) rightFrame
  have rightGlobals : rightTarget.globals = rightFilled.globals := congrArg (fun state => state.globals) rightFrame
  have rightClockEq : rightTarget.clock = rightFilled.clock := congrArg (fun state => state.clock) rightFrame
  have finalBuilt := Layout32.built_fields leftFilled leftTarget plan bits scratch finalCount input logical rfl rfl rfl filledBuilt
  have finalRecords : Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) := ⟨filledRecords.pointers, filledRecords.lengths⟩
  have finalGlobals : leftTarget.globals = rightTarget.globals := by
    change leftFilled.globals = rightTarget.globals
    rw [rightGlobals]
    exact (congrArg (fun state => state.globals) leftControl).trans
      (preparedGlobals.trans (congrArg (fun state => state.globals) rightControl).symm)
  have finalFfi : leftTarget.ffi = rightTarget.ffi := by change leftFilled.ffi = rightTarget.ffi; rw [rightFfi]; exact filledFfi
  have finalMemory : MemoryRegion.Agree region leftTarget.memory rightTarget.memory := by
    intro query inside
    change leftFilled.memory query = rightTarget.memory query
    rw [rightMemory]
    exact filledMemory query inside
  have finalLeftControl : KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl (prepared source plan) := by
    change KeccakAbsorb.hashControl (finishScope source plan leftFilled) = _
    rw [finishScope, KeccakAbsorb.hashControl_restore, KeccakAbsorb.hashControl_restore]
    exact leftControl
  have finalRightControl : KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl (Constructor.preparedState right plan) := by
    have frame := congrArg KeccakAbsorb.hashControl rightFrame
    have relation : KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl rightFilled := by
      simpa only [KeccakAbsorb.hashControl_empty] using frame
    exact relation.trans rightControl
  refine ⟨finalCount, input, logical, keyFor, leftTarget, rightTarget, root, ?_, ?_, finalBuilt,
    filledHistory, filledMatching, filledLength, finalRecords, ?_, ?_,
    QueryMemory.represents_of_fields rightFilled rightTarget rightMemory.symm rightDomain.symm rightEndian.symm _ _ _ _ _ filledRep,
    finalLeftControl, finalRightControl, ?_, ?_, ?_, ?_, finalGlobals, finalFfi, finalMemory,?_,?_,?support⟩
  · rw [leftFilledRun] at leftPrepare
    exact leftPrepare
  · rw [rightFilledRun] at rightPrepare
    exact rightPrepare
  · rw [rightDomain]; exact filledRootMapped
  · rw [rightMemory]; exact filledRootWord
  · change leftFilled.clock ≤ source.clock
    rw [leftEntryClock] at leftUpper
    omega
  · change source.clock - tablePopulatePrice maximum plan ≤ leftFilled.clock
    rw [leftEntryClock] at leftLower
    unfold tablePopulatePrice
    omega
  · rw [rightClockEq]
    rw [rightEntryClock] at rightUpper
    omega
  · rw [rightClockEq]
    rw [rightEntryClock] at rightLower
    unfold Constructor.tablePopulatePrice
    omega

  · intro query saved
    change leftFilled.memory query=source.memory query
    rw [leftSaved query saved]
    exact TableNew.result_earlier _ _ plan ready query (safeBefore query saved)
  · intro query saved
    rw [rightMemory,rightSaved query saved]
    exact TableNew.result_earlier _ _ plan ready query (safeBefore query saved)

  case support =>
    intro query read
    exact filledSupport query ((QueryMemory.reads_stable rightFilled rightTarget _ _ _ root
      (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals plan.count))
      (by intro address member;exact congrFun rightMemory.symm address) query).mpr read)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_table_populate_supported

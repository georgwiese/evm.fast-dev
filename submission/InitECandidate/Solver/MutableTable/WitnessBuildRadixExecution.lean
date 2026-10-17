import InitECandidate.Solver.MutableTable.WitnessBuildRadixTable
import InitECandidate.Solver.MutableTable.WitnessBuildExecution
import InitECandidate.Solver.WitnessRadix.CapacityPairedEntry

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Entire actual original/candidate witness constructors, from decoded input
and allocated-buffer premises. Capacity, allocation, every hash/update, radix
indexing, returns and scopes are derived; histories and observables agree. -/
theorem paired_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (records table count maximum : Nat)
    (recordsLower : 2701131776 ≤ records) (recordsBefore : records + 16*count ≤ table)
    (recordsAligned : records % 8 = 0) (tableAligned : table % 8 = 0)
    (room : table + 72 + 57*(4*count+4) + 7 ≤ 33806089496)
    (recordsLocal : source.locals.lookup (ofString "slice_arr") = some (.val (.word (BitVec.ofNat 64 records))))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (rightTableCode : right.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (leftAllocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (rightAllocCode : right.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (pointers : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i)) = .word (sliceFor (BitVec.ofNat 64 i)).1)
    (lengths : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i+8)) = .word (sliceFor (BitVec.ofNat 64 i)).2)
    (context : ∀ capacity, Context source (Constructor.allocationPlan records table count capacity)
      (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightEnvironment : Keccak256.Environment right stp pad)
    (rightHashCode : right.code.lookup (ofString "keccak256") = some (Keccak256.formals, Keccak256.body, .one))
    (helperCode : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (locals : source.locals = right.locals) (globals : source.globals = right.globals)
    (endian : source.be = right.be) (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (same : MemoryRegion.Agree region source.memory right.memory)
    (before : ∀ query, region query → query.toNat < table)
    (recordPublic : ∀ i < count, region (byteAddress (BitVec.ofNat 64 records) (16*i)) ∧
      region (byteAddress (BitVec.ofNat 64 records) (16*i+8)))
    (buffers : ∀ i < count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (leftClock : wholePrice maximum count ≤ source.clock)
    (rightClock : Constructor.wholePrice maximum count ≤ right.clock) :
    ∃ bits finalCount input logical keyFor leftTarget rightTarget root,
      let plan := Constructor.allocationPlan records table count (2^bits)
      2 ≤ bits ∧ bits ≤ 32 ∧ AllocatedLayout.Ready plan ∧
      evaluateHOLFiniteState source body =
        (some (.returned (.val (.word (BitVec.ofNat 64 table)))), leftTarget) ∧
      evaluateHOLFiniteState right Constructor.body =
        (some (.returned (.val (.word (BitVec.ofNat 64 table)))), rightTarget) ∧
      Layout32.Built bits leftTarget plan scratch finalCount input logical ∧ History plan input ∧
      KeysMatch plan keyFor input ∧ input.length = count ∧ Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      rightTarget.memaddrs (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) ∧
      rightTarget.memory (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) = .word root ∧
      QueryMemory.Represents rightTarget (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
        (AllocatedLayout.layout plan).vals root
        (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals count)) ∧
      KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word
          (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl {right with
        globals := right.globals.update (ofString "heap_ptr", .val (.word
          (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      leftTarget.clock ≤ source.clock ∧ source.clock - wholePrice maximum count ≤ leftTarget.clock ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - Constructor.wholePrice maximum count ≤ rightTarget.clock ∧
      leftTarget.globals = rightTarget.globals ∧ leftTarget.ffi = rightTarget.ffi ∧
      MemoryRegion.Agree region leftTarget.memory rightTarget.memory := by
  classical
  have small := Capacity.count_small_of_records records table count recordsLower recordsBefore (by omega)
  obtain ⟨leftCap, rightCap, paid, bits, leftPrefix, rightPrefix, paidBound, bitsLow, bitsTop, sufficient, capBound,
    leftCapLocal, rightCapLocal, capLocals, leftFrame, rightFrame, leftOther, rightOther⟩ :=
    Capacity.declare_paired source right count small countLocal locals (by unfold wholePrice at leftClock; omega)
      (by unfold Constructor.wholePrice at rightClock; omega) allocatedTail Constructor.allocatedTail
  have leftPrefixRun : evaluateHOLFiniteState source body =
      (let output := evaluateHOLFiniteState leftCap allocatedTail; (output.1, restore source "cap" output.2)) := by
    simpa only [body_shape, allocatedTail] using leftPrefix
  have rightPrefixRun : evaluateHOLFiniteState right Constructor.body =
      (let output := evaluateHOLFiniteState rightCap Constructor.allocatedTail; (output.1, restore right "cap" output.2)) := by
    simpa only [Constructor.body_shape, Constructor.allocatedTail] using rightPrefix
  let plan := Constructor.allocationPlan records table count (2^bits)
  have shape := Capacity.power_shape bits bitsLow
  have ready : AllocatedLayout.Ready plan := Constructor.allocation_ready records table count (2^bits)
    recordsLower recordsBefore recordsAligned tableAligned room sufficient capBound shape
  have leftCapClock : leftCap.clock = source.clock - paid := congrArg (fun state => state.clock) leftFrame
  have rightCapClock : rightCap.clock = right.clock - paid := congrArg (fun state => state.clock) rightFrame
  have leftMemory : leftCap.memory = source.memory := congrArg (fun state => state.memory) leftFrame
  have rightMemory : rightCap.memory = right.memory := congrArg (fun state => state.memory) rightFrame
  have leftCodes : leftCap.code = source.code := congrArg (fun state => state.code) leftFrame
  have rightCodes : rightCap.code = right.code := congrArg (fun state => state.code) rightFrame
  have leftGlobals : leftCap.globals = source.globals := congrArg (fun state => state.globals) leftFrame
  have rightGlobals : rightCap.globals = right.globals := congrArg (fun state => state.globals) rightFrame
  have leftCapFfi : leftCap.ffi = source.ffi := congrArg (fun state => state.ffi) leftFrame
  have rightCapFfi : rightCap.ffi = right.ffi := congrArg (fun state => state.ffi) rightFrame
  have leftEndian : leftCap.be = source.be := congrArg (fun state => state.be) leftFrame
  have rightEndian : rightCap.be = right.be := congrArg (fun state => state.be) rightFrame
  have leftHashControl : KeccakAbsorb.hashControl leftCap = KeccakAbsorb.hashControl source := by
    have frame := congrArg KeccakAbsorb.hashControl leftFrame
    simpa only [KeccakAbsorb.hashControl_empty, KeccakAbsorb.hashControl_clock] using frame
  have rightHashControl : KeccakAbsorb.hashControl rightCap = KeccakAbsorb.hashControl right := by
    have frame := congrArg KeccakAbsorb.hashControl rightFrame
    simpa only [KeccakAbsorb.hashControl_empty, KeccakAbsorb.hashControl_clock] using frame
  have capContext := Context.of_control source leftCap plan _ stp pad scratch maximum leftHashControl (context (2^bits))
  have capEnvironment := Keccak256.Environment.of_control right rightCap stp pad rightHashControl rightEnvironment
  have capRecords : Records leftCap plan (fun i => sliceFor (BitVec.ofNat 64 i)) := by
    constructor
    · intro i inside
      rw [leftMemory, record_backing]
      change source.memory (byteAddress (BitVec.ofNat 64 records) (16*i+0)) = _
      simpa only [Nat.add_zero] using pointers i inside
    · intro i inside
      rw [leftMemory, record_backing]
      exact lengths i inside
  have capMemory : MemoryRegion.Agree region leftCap.memory rightCap.memory := by
    intro query inside
    rw [leftMemory, rightMemory]
    exact same query inside
  have leftPrice : tablePopulatePrice maximum plan + 30 ≤ wholePrice maximum count := by
    have cost := Constructor.table_price_bound (2^bits)
    unfold tablePopulatePrice wholePrice
    change TableNew.price (2^bits)+1+(recordPrice maximum count+1)*count+30 ≤
      (recordPrice maximum count+1)*count+4*count+46
    omega
  have rightPrice : Constructor.tablePopulatePrice maximum plan + 30 ≤ Constructor.wholePrice maximum count :=
    Constructor.table_populate_price_bound maximum records table count (2^bits) capBound
  obtain ⟨finalCount, input, logical, keyFor, leftFilled, rightFilled, root, leftTableRun, rightTableRun,
    filledBuilt, filledHistory, filledMatching, filledLength, filledRecords, rootMapped, rootWord, represented,
    leftControl, rightControl, leftUpper, leftLower, rightUpper, rightLower, filledGlobals, filledFfi, filledMemory⟩ :=
    paired_table_populate leftCap rightCap plan ready bits maximum (by omega) rfl shape leftCapLocal
      (by rw [leftGlobals]; exact heap) (by rw [leftCodes]; exact leftTableCode) (by rw [rightCodes]; exact rightTableCode)
      (by rw [leftCodes]; exact leftAllocCode) (by rw [rightCodes]; exact rightAllocCode) sliceFor stp pad scratch
      ((leftOther (ofString "slice_arr") (by decide)).trans recordsLocal)
      ((leftOther (ofString "n") (by decide)).trans countLocal) capRecords capContext capEnvironment
      (by rw [rightCodes]; exact rightHashCode) (by rw [rightCodes]; exact helperCode) capLocals
      (leftGlobals.trans (globals.trans rightGlobals.symm)) (leftEndian.trans (endian.trans rightEndian.symm))
      (leftCapFfi.trans (ffi.trans rightCapFfi.symm)) region capMemory before recordPublic buffers
      (by rw [leftCapClock]; omega) (by rw [rightCapClock]; omega)
  change evaluateHOLFiniteState leftCap allocatedTail =
    (some (.returned (.val (.word (BitVec.ofNat 64 table)))), leftFilled) at leftTableRun
  change evaluateHOLFiniteState rightCap Constructor.allocatedTail =
    (some (.returned (.val (.word (BitVec.ofNat 64 table)))), rightFilled) at rightTableRun
  let leftTarget := restore source "cap" leftFilled
  let rightTarget := restore right "cap" rightFilled
  have finalBuilt := Layout32.built_fields leftFilled leftTarget plan bits scratch finalCount input logical rfl rfl rfl filledBuilt
  have finalRecords : Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) := ⟨filledRecords.pointers, filledRecords.lengths⟩
  have leftInitial : KeccakAbsorb.hashControl (prepared leftCap plan) = KeccakAbsorb.hashControl {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word
        (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} := by
    have updated := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with
      globals := state.globals.update (ofString "heap_ptr", .val (.word
        (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))}) leftHashControl
    exact updated
  have rightInitial : KeccakAbsorb.hashControl (Constructor.preparedState rightCap plan) = KeccakAbsorb.hashControl {right with
      globals := right.globals.update (ofString "heap_ptr", .val (.word
        (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} := by
    have updated := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with
      globals := state.globals.update (ofString "heap_ptr", .val (.word
        (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))}) rightHashControl
    exact updated
  refine ⟨bits, finalCount, input, logical, keyFor, leftTarget, rightTarget, root, bitsLow, bitsTop, ready,
    ?_, ?_, finalBuilt, filledHistory, filledMatching, filledLength, finalRecords, rootMapped, rootWord,
    QueryMemory.represents_of_fields rightFilled rightTarget rfl rfl rfl _ _ _ _ _ represented,
    leftControl.trans leftInitial, rightControl.trans rightInitial, ?_, ?_, ?_, ?_, filledGlobals, filledFfi, filledMemory⟩
  · rw [leftPrefixRun, leftTableRun]
  · rw [rightPrefixRun, rightTableRun]
  · change leftFilled.clock ≤ source.clock
    rw [leftCapClock] at leftUpper
    omega
  · change source.clock - wholePrice maximum count ≤ leftFilled.clock
    rw [leftCapClock] at leftLower
    omega
  · change rightFilled.clock ≤ right.clock
    rw [rightCapClock] at rightUpper
    omega
  · change right.clock - Constructor.wholePrice maximum count ≤ rightFilled.clock
    rw [rightCapClock] at rightLower
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_execute

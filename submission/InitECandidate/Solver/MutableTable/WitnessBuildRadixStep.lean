import InitECandidate.Solver.MutableTable.WitnessBuildRecordHash
import InitECandidate.Solver.MutableTable.WitnessBuildContext
import InitECandidate.Solver.WitnessRadix.ConstructorRecordHash
import InitECandidate.Solver.WitnessRadix.ConstructorPublicFrame
import InitECandidate.Solver.WitnessRadix.Keccak256BufferAgreement

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

/-- One actual original/radix witness-construction iteration observes the
same hash key, extends both physical representations and preserves public
memory and FFI agreement. Private tables and unrelated code may differ. -/
theorem paired_record_step (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (layout : BackingLayout.Layout) (valid : BackingLayout.Valid layout)
    (mapped : BackingLayout.Mapped right layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (stp pad scratch : BitVec 64)
    (index count bits maximum : Nat) (smallBits : bits < 64) (power : plan.capacity = 2^bits)
    (input : List (Find.Key32 × BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical)
    (processed : input.length = index) (leftInside : index < plan.count) (rightInside : index < layout.count)
    (leftLocals : Locals source plan index)
    (rightLocals : Constructor.Locals right layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index))
    (records : Records source plan (fun i => sliceFor (BitVec.ofNat 64 i)))
    (prefixData : Constructor.Prefix right layout keyFor index)
    (fixedData : Constructor.FixedData right layout sliceFor)
    (leftContext : Context source plan (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightContext : Constructor.HashContext right layout sliceFor stp pad scratch maximum)
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (buffers : Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 index)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (same : MemoryRegion.Agree region source.memory right.memory)
    (leftBefore : ∀ query, region query → query.toNat < plan.table)
    (rightBefore : ∀ query, region query → ∀ entry ∈ Constructor.writeAddresses index,
      query.toNat < (BackingLayout.base layout entry.1).toNat)
    (leftClock : recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat index ≤ source.clock)
    (rightClock : Constructor.recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat ≤ right.clock) :
    ∃ key slot nextCount leftTarget rightTarget,
      slot < plan.capacity ∧ count ≤ nextCount ∧ nextCount ≤ count + 1 ∧
      evaluateHOLFiniteState source recordBody = (none, leftTarget) ∧
      evaluateHOLFiniteState right Constructor.recordBody = (none, rightTarget) ∧
      Layout32.Built bits leftTarget plan scratch nextCount (input ++ [(key, recordAddress plan index)])
        (Placement.put logical slot key (recordAddress plan index)) ∧
      Constructor.Prefix rightTarget layout (Constructor.setKey keyFor index key) (index + 1) ∧
      Locals leftTarget plan (index + 1) ∧
      Constructor.Locals rightTarget layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 (index + 1)) ∧
      Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      Constructor.FixedData rightTarget layout sliceFor ∧ BackingLayout.Mapped rightTarget layout ∧
      KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl right ∧
      leftTarget.clock ≤ source.clock ∧ source.clock - recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat index ≤ leftTarget.clock ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - Constructor.recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat ≤ rightTarget.clock ∧
      leftTarget.ffi = rightTarget.ffi ∧ MemoryRegion.Agree region leftTarget.memory rightTarget.memory ∧
      (∀ name, ofString "i" ≠ name → leftTarget.locals.lookup name = source.locals.lookup name) ∧
      (∀ name, ofString "i" ≠ name → rightTarget.locals.lookup name = right.locals.lookup name) := by
  classical
  let slice := sliceFor (BitVec.ofNat 64 index)
  change Keccak256.price slice.2.toNat + 7 * index + 8 ≤ source.clock at leftClock
  change Keccak256.price slice.2.toNat + 3 ≤ right.clock at rightClock
  have arenas := leftContext.buffers index leftInside
  have leftArgs := hash_arguments source plan ready leftContext.environment.domain _ records index leftInside
    leftLocals scratch leftContext.global
  have rightArgs := Constructor.hash_arguments right layout mapped sliceFor fixedData index rightInside
    rightLocals scratch rightContext.scratchGlobal
  have domain : source.memaddrs = right.memaddrs :=
    leftContext.environment.domain.trans rightContext.environment.domain.symm
  have endian : source.be = right.be := leftContext.little.trans rightContext.little.symm
  have lengthSmall : slice.2.toNat + 136 < 2^64 := by
    dsimp only [slice]
    have := arenas.inputArena.upper
    omega
  obtain ⟨leftHash, rightHash, leftHashRun, rightHashRun, leftHashLocals, rightHashLocals,
    leftHashUpper, leftHashLower, rightHashUpper, rightHashLower, leftHashControl, rightHashControl,
    hashFfi, hashMemory, leftHashAway, rightHashAway⟩ :=
    Keccak256.paired_call_execute source right Constructor.hashArguments Constructor.hashArguments stp slice.1 pad scratch slice.2.toNat
      leftArgs rightArgs leftContext.keccakCode rightContext.code
      (Keccak256.allocated_entry source stp slice.1 pad scratch slice.2.toNat leftContext.environment arenas)
      (Keccak256.allocated_entry right stp slice.1 pad scratch slice.2.toNat rightContext.environment arenas)
      domain endian ffi region same
      (Keccak256.block_reads_of_buffers region stp slice.1 pad scratch slice.2.toNat buffers)
      (by intro offset inside; exact (buffers.state offset inside).2)
      (Keccak256.tail_reads_of_buffers region stp slice.1 pad scratch slice.2.toNat
        (136 * (slice.2.toNat / 136)) (by have := Nat.mod_add_div slice.2.toNat 136; omega) buffers)
      lengthSmall (by omega) (by omega)
  obtain ⟨leftKey, slot, nextCount, leftTarget, slotInside, countLower, countUpper,
    leftRun, nextBuilt, nextLeftLocals, nextRecords, leftControl, leftUpper, leftLower, leftOther,
    leftKeyEq, leftFfi, leftFrame⟩ :=
    record_step_with_hash source plan ready leftContext.environment.domain scratch count index input logical bits smallBits power
      built processed leftInside leftLocals _ records stp pad leftContext.global arenas leftContext.before leftContext.aligned leftContext.little
      leftContext.hashCode leftContext.copyCode leftContext.insertCode leftContext.memeqCode leftContext.findCode leftContext.setCode
      leftHash leftHashRun leftHashLocals leftHashUpper leftHashLower leftHashControl leftHashAway leftClock
  obtain ⟨rightKey, rightTarget, rightRun, nextPrefix, nextFixed, nextMapped, nextRightLocals,
    rightControl, rightUpper, rightLower, rightOther, rightKeyEq, rightExact, rightFfi⟩ :=
    Constructor.record_step_with_hash right layout valid mapped keyFor sliceFor index rightInside rightLocals prefixData fixedData
      stp pad scratch rightContext.scratchGlobal rightContext.environment arenas rightContext.before
      rightContext.scratchAligned rightContext.little rightHash rightHashRun rightHashLocals rightHashUpper rightHashLower
      rightHashControl rightHashAway rightClock
  have digestWords := Keccak256.digest_words_agree leftHash rightHash region stp slice.1 pad scratch slice.2.toNat buffers hashMemory
  have keys : leftKey = rightKey := leftKeyEq.trans ((congrArg WordKeys.key digestWords).trans rightKeyEq.symm)
  rw [← keys] at nextPrefix
  have finalFfi := leftFfi.trans (hashFfi.trans rightFfi.symm)
  have finalMemory : MemoryRegion.Agree region leftTarget.memory rightTarget.memory := by
    intro query inRegion
    have rightFrame : rightTarget.memory query = rightHash.memory query := by
      rw [rightExact]
      exact Constructor.suffix_memory_before rightHash layout valid index rightInside _ query (rightBefore query inRegion)
    exact (leftFrame query (leftBefore query inRegion)).trans ((hashMemory query inRegion).trans rightFrame.symm)
  exact ⟨leftKey, slot, nextCount, leftTarget, rightTarget, slotInside, countLower, countUpper,
    leftRun, rightRun, nextBuilt, nextPrefix, nextLeftLocals, nextRightLocals, nextRecords, nextFixed, nextMapped,
    leftControl, rightControl, leftUpper, leftLower, rightUpper, rightLower, finalFfi, finalMemory, leftOther, rightOther⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_record_step

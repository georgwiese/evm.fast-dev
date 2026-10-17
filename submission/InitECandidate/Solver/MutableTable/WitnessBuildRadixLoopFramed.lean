import InitECandidate.Solver.MutableTable.WitnessBuildRadixStepFramed
import InitECandidate.Solver.MutableTable.WitnessBuildKeyHistory
import InitECandidate.Solver.WitnessRadix.ConstructorRecordLoop

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

/-- Both actual witness-record loops preserve each program's own safe words,
including earlier private dictionaries, while observing identical keys and FFI events.
The original insertion history exactly matches the radix key prefix, including
duplicate digests. Public buffer ownership remains an explicit premise. -/
theorem paired_record_loop_framed (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (layout : BackingLayout.Layout) (valid : BackingLayout.Valid layout) (counts : layout.count = plan.count)
    (sliceFor : BitVec 64  →  Graph.Slice) (stp pad scratch : BitVec 64)
    (bits maximum index remaining count : Nat) (smallBits : bits < 64) (power : plan.capacity = 2^bits)
    (input : List (Find.Key32 × BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (keyFor : BitVec 64  →  ByteKeys.Key)
    (sizeEq : index + remaining = plan.count) (processed : input.length = index)
    (built : Layout32.Built bits source plan scratch count input logical)
    (history : History plan input) (matching : KeysMatch plan keyFor input)
    (leftLocals : Locals source plan index) (records : Records source plan (fun i => sliceFor (BitVec.ofNat 64 i)))
    (mapped : BackingLayout.Mapped right layout)
    (rightLocals : Constructor.Locals right layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index))
    (rightCount : right.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))))
    (prefixData : Constructor.Prefix right layout keyFor index) (fixedData : Constructor.FixedData right layout sliceFor)
    (leftContext : Context source plan (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightContext : Constructor.HashContext right layout sliceFor stp pad scratch maximum)
    (ffi : source.ffi = right.ffi) (region : BitVec 64  →  Prop)
    (same : MemoryRegion.Agree region source.memory right.memory)
    (buffers : ∀ i < plan.count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (leftBefore : ∀ query, region query  →  query.toNat < plan.table)
    (rightBefore : ∀ query, region query  →  ∀ i < plan.count, ∀ entry ∈ Constructor.writeAddresses i,
      query.toNat < (BackingLayout.base layout entry.1).toNat)
    (safe : BitVec 64  →  Prop)
    (leftSafe : ∀ query,safe query → query.toNat<plan.table)
    (rightSafe : ∀ query,safe query → ∀ i<plan.count,∀ entry ∈ Constructor.writeAddresses i,
      query.toNat<(BackingLayout.base layout entry.1).toNat)
    (protectedSafe : ∀ query,safe query → Keccak256.Protected stp pad scratch query)
    (leftClock : (recordPrice maximum plan.count + 1) * remaining ≤ source.clock)
    (rightClock : (Constructor.recordPrice maximum + 1) * remaining ≤ right.clock) :
    ∃ finalCount finalInput finalLogical finalKeys leftOutput rightOutput,
      evaluateHOLFiniteState source recordLoop = (none, leftOutput) ∧
      evaluateHOLFiniteState right Constructor.recordLoop = (none, rightOutput) ∧
      Layout32.Built bits leftOutput plan scratch finalCount finalInput finalLogical ∧
      History plan finalInput ∧ KeysMatch plan finalKeys finalInput ∧ finalInput.length = plan.count ∧
      Constructor.Prefix rightOutput layout finalKeys layout.count ∧
      Locals leftOutput plan plan.count ∧ Records leftOutput plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      Constructor.FixedData rightOutput layout sliceFor ∧ BackingLayout.Mapped rightOutput layout ∧
      Constructor.Locals rightOutput layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 layout.count) ∧
      KeccakAbsorb.hashControl leftOutput = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightOutput = KeccakAbsorb.hashControl right ∧
      leftOutput.clock ≤ source.clock ∧ source.clock - (recordPrice maximum plan.count + 1) * remaining ≤ leftOutput.clock ∧
      rightOutput.clock ≤ right.clock ∧ right.clock - (Constructor.recordPrice maximum + 1) * remaining ≤ rightOutput.clock ∧
      leftOutput.ffi = rightOutput.ffi ∧ MemoryRegion.Agree region leftOutput.memory rightOutput.memory ∧
      (∀ name, ofString "i" ≠ name  →  leftOutput.locals.lookup name = source.locals.lookup name) ∧
      (∀ name, ofString "i" ≠ name  →  rightOutput.locals.lookup name = right.locals.lookup name) ∧
      (∀ query,safe query → leftOutput.memory query=source.memory query) ∧
      (∀ query,safe query → rightOutput.memory query=right.memory query) := by
  classical
  have countSmall : plan.count < 2^64 := by have := BackingLayout.count_small layout valid; omega
  induction remaining generalizing source right index count input logical keyFor with
  | zero =>
    have leftEq : index = plan.count := by omega
    have rightEq : index = layout.count := by omega
    have leftTest := Zero.tail_condition source index plan.count countSmall (by omega) leftLocals.index leftLocals.count
    have rightTest := Zero.tail_condition right index layout.count (by omega) (by omega) rightLocals.indexLocal rightCount
    change @evalHOLFinite 64 Guest.HostMemory _ source (fun q => Classical.propDecidable (source.memaddrs q)) Constructor.condition =
      some (.val (.word (if index < plan.count then 1#64 else 0#64))) at leftTest
    change @evalHOLFinite 64 Guest.HostMemory _ right (fun q => Classical.propDecidable (right.memaddrs q)) Constructor.condition =
      some (.val (.word (if index < layout.count then 1#64 else 0#64))) at rightTest
    rw [if_neg (by omega)] at leftTest rightTest
    refine ⟨count, input, logical, keyFor, source, right, ?_, ?_, built, history, matching, by omega,
      ?_, ?_, records, fixedData, mapped, ?_, rfl, rfl, Nat.le_refl _, by simp, Nat.le_refl _, by simp, ffi, same, ?_, ?_,(by intros;rfl),(by intros;rfl)⟩
    · rw [recordLoop, evaluateHOLFiniteState_while_total, leftTest]; simp
    · rw [Constructor.loop_shape, evaluateHOLFiniteState_while_total, rightTest]; simp
    · simpa only [rightEq] using prefixData
    · simpa only [leftEq] using leftLocals
    · simpa only [rightEq] using rightLocals
    · intro name different; rfl
    · intro name different; rfl
  | succ remaining ih =>
    simp only [Nat.mul_succ] at leftClock rightClock
    have leftInside : index < plan.count := by omega
    have rightInside : index < layout.count := by omega
    let leftEntry := decClockHOLFinite source
    let rightEntry := decClockHOLFinite right
    have entryBuilt := Layout32.built_fields source leftEntry plan bits scratch count input logical rfl rfl rfl built
    have entryRecords := Records.of_earlier source leftEntry plan ready _ (by intros; rfl) records
    have entryLeftLocals : Locals leftEntry plan index :=
      ⟨leftLocals.table, leftLocals.records, leftLocals.count, leftLocals.index⟩
    have leftEntryContext := Context.of_control source leftEntry plan _ stp pad scratch maximum rfl leftContext
    have entryFrame : Constructor.PoolFrame right rightEntry layout := ⟨rfl, rfl, by intros; rfl⟩
    have entryMapped := Constructor.PoolFrame.mapped right rightEntry layout entryFrame mapped
    have entryPrefix := Constructor.PoolFrame.prefix right rightEntry layout valid entryFrame keyFor index (by omega) prefixData
    have entryFixed := Constructor.PoolFrame.fixed_data right rightEntry layout entryFrame sliceFor fixedData
    have entryRightLocals : Constructor.Locals rightEntry layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index) :=
      ⟨rightLocals.keysLocal, rightLocals.valsLocal, rightLocals.orderLocal, rightLocals.recordsLocal, rightLocals.indexLocal⟩
    have rightEntryContext := Constructor.HashContext.of_control right rightEntry layout sliceFor stp pad scratch maximum rfl rightContext
    have leftPrice := recordPrice_mono (sliceFor (BitVec.ofNat 64 index)).2.toNat maximum index plan.count
      (leftContext.lengthBound index leftInside) (Nat.le_of_lt leftInside)
    have rightPrice := Constructor.recordPrice_mono (sliceFor (BitVec.ofNat 64 index)).2.toNat maximum
      (rightContext.lengthBound index rightInside)
    obtain ⟨key, slot, nextCount, leftNext, rightNext, slotInside, countLower, countUpper, leftBody, rightBody,
      nextBuilt, nextPrefix, nextLeftLocals, nextRightLocals, nextRecords, nextFixed, nextMapped,
      leftBodyControl, rightBodyControl, leftUpper, leftLower, rightUpper, rightLower, nextFfi, nextMemory, leftOther, rightOther,leftSaved,rightSaved⟩ :=
      paired_record_step_framed leftEntry rightEntry plan ready layout valid entryMapped keyFor sliceFor stp pad scratch
        index count bits maximum smallBits power input logical entryBuilt processed leftInside rightInside entryLeftLocals entryRightLocals
        entryRecords entryPrefix entryFixed leftEntryContext rightEntryContext ffi region (buffers index leftInside) same leftBefore
        (by intro q inRegion; exact rightBefore q inRegion index leftInside)
        safe leftSafe (by intro q saved;exact rightSafe q saved index leftInside) protectedSafe
        (by change recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat index ≤ source.clock - 1; omega)
        (by change Constructor.recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat ≤ right.clock - 1; omega)
    have nextHistory : History plan (input ++ [(key, recordAddress plan index)]) := by
      simpa only [processed] using History.snoc input history key (by omega)
    have nextMatch : KeysMatch plan (Constructor.setKey keyFor index key) (input ++ [(key, recordAddress plan index)]) := by
      simpa only [processed] using KeysMatch.snoc plan layout valid keyFor input matching key (by omega)
    have nextLeftContext := Context.of_control leftEntry leftNext plan _ stp pad scratch maximum leftBodyControl leftEntryContext
    have nextRightContext := Constructor.HashContext.of_control rightEntry rightNext layout sliceFor stp pad scratch maximum rightBodyControl rightEntryContext
    have nextRightCount := (rightOther (ofString "n") (by decide)).trans rightCount
    have leftBudget : source.clock - 1 - recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat index ≤ leftNext.clock := leftLower
    have rightBudget : right.clock - 1 - Constructor.recordPrice (sliceFor (BitVec.ofNat 64 index)).2.toNat ≤ rightNext.clock := rightLower
    obtain ⟨finalCount, finalInput, finalLogical, finalKeys, leftOutput, rightOutput,
      leftTail, rightTail, finalBuilt, finalHistory, finalMatch, finalLength, finalPrefix, finalLeftLocals,
      finalRecords, finalFixed, finalMapped, finalRightLocals, leftTailControl, rightTailControl,
      leftTailUpper, leftTailLower, rightTailUpper, rightTailLower, finalFfi, finalMemory, finalLeftOther, finalRightOther,leftTailSaved,rightTailSaved⟩ :=
      ih leftNext rightNext (index + 1) nextCount (input ++ [(key, recordAddress plan index)])
        (Placement.put logical slot key (recordAddress plan index)) (Constructor.setKey keyFor index key)
        (by omega) (by simp only [List.length_append, List.length_singleton, processed]) nextBuilt nextHistory nextMatch
        nextLeftLocals nextRecords nextMapped nextRightLocals nextRightCount nextPrefix nextFixed
        nextLeftContext nextRightContext nextFfi nextMemory (by omega) (by omega)
    refine ⟨finalCount, finalInput, finalLogical, finalKeys, leftOutput, rightOutput, ?_, ?_, finalBuilt,
      finalHistory, finalMatch, finalLength, finalPrefix, finalLeftLocals, finalRecords, finalFixed, finalMapped, finalRightLocals,
      leftTailControl.trans leftBodyControl, rightTailControl.trans rightBodyControl, ?_, ?_, ?_, ?_,
      finalFfi, finalMemory, ?_, ?_,?_,?_⟩
    · have test := Zero.tail_condition source index plan.count countSmall (by omega) leftLocals.index leftLocals.count
      change @evalHOLFinite 64 Guest.HostMemory _ source (fun q => Classical.propDecidable (source.memaddrs q)) Constructor.condition =
        some (.val (.word (if index < plan.count then 1#64 else 0#64))) at test
      rw [if_pos leftInside] at test
      have unfolded := evaluateHOLFiniteState_while_total source Constructor.condition recordBody
      rw [test] at unfolded
      simp only at unfolded
      rw [if_pos (show 1#64 ≠ (0 : BitVec 64) by decide), if_neg (show source.clock ≠ 0 by omega), leftBody,
        StateSteps.fixed_clock leftEntry leftNext none leftUpper] at unfolded
      exact unfolded.trans leftTail
    · have test := Zero.tail_condition right index layout.count (by omega) (by omega) rightLocals.indexLocal rightCount
      change @evalHOLFinite 64 Guest.HostMemory _ right (fun q => Classical.propDecidable (right.memaddrs q)) Constructor.condition =
        some (.val (.word (if index < layout.count then 1#64 else 0#64))) at test
      rw [if_pos rightInside] at test
      have unfolded := evaluateHOLFiniteState_while_total right Constructor.condition Constructor.recordBody
      rw [test] at unfolded
      simp only at unfolded
      rw [if_pos (show 1#64 ≠ (0 : BitVec 64) by decide), if_neg (show right.clock ≠ 0 by omega), rightBody,
        StateSteps.fixed_clock rightEntry rightNext none rightUpper] at unfolded
      rw [Constructor.loop_shape] at rightTail ⊢
      exact unfolded.trans rightTail
    · change leftNext.clock ≤ source.clock - 1 at leftUpper
      omega
    · simp only [Nat.mul_succ]
      omega
    · change rightNext.clock ≤ right.clock - 1 at rightUpper
      omega
    · simp only [Nat.mul_succ]
      omega
    · intro name different
      exact (finalLeftOther name different).trans (leftOther name different)
    · intro name different
      exact (finalRightOther name different).trans (rightOther name different)
    · intro query saved
      exact (leftTailSaved query saved).trans (leftSaved query saved)
    · intro query saved
      exact (rightTailSaved query saved).trans (rightSaved query saved)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_record_loop_framed

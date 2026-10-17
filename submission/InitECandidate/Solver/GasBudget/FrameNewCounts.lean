import InitECandidate.Solver.GasBudget.FrameNewSuffixProgram

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def countedFirst (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame count : BitVec 64) :=
  {WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} "acc_n" count with
    memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes frame (firstCountFields count))}
noncomputable def countedFinal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame addressCount keyCount empty : BitVec 64) :=
  let first := countedFirst source frame addressCount
  {WitnessRadix.QueryBranch.bind {first with clock := first.clock - 1} "acc_n" keyCount with
    memory := WitnessRadix.WordWrites.write first.memory (FieldStores.writes frame (finalFields keyCount empty))}

theorem count_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame addressCount keyCount empty query : BitVec 64)
    (away : ∀ offset ∈ ([264, 272, 120, 144, 216] : List Nat), query ≠ frame + BitVec.ofNat 64 offset) :
    (countedFinal source frame addressCount keyCount empty).memory query = source.memory query := by
  change WitnessRadix.WordWrites.write
    (WitnessRadix.WordWrites.write source.memory (FieldStores.writes frame (firstCountFields addressCount)))
    (FieldStores.writes frame (finalFields keyCount empty)) query = source.memory query
  rw [WitnessRadix.WordWrites.write_away, WitnessRadix.WordWrites.write_away]
  · simpa [FieldStores.writes, firstCountFields] using away 264 (by simp)
  · simp only [FieldStores.writes, finalFields, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨away 272 (by simp), away 120 (by simp), away 144 (by simp), away 216 (by simp)⟩

/-- The real two access-set count calls, their frame stores, the two global
empty-list reads and the final return. Input cells are protected explicitly;
no successful helper execution or memory-preservation oracle is assumed. -/
theorem counts_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message addresses keys addressCount keyCount empty : BitVec 64)
    (frameLocal : source.locals.lookup (ofString "e") = some (.val (.word frame)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (code : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one))
    (frameMapped : ∀ offset ∈ ([264, 272, 120, 144, 216] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (addressMapped : source.memaddrs (message + 152#64)) (addressCell : source.memory (message + 152#64) = .word addresses)
    (keyMapped : source.memaddrs (message + 160#64)) (keyCell : source.memory (message + 160#64) = .word keys)
    (addressCountMapped : source.memaddrs (addresses + 24#64)) (addressCountCell : source.memory (addresses + 24#64) = .word addressCount)
    (keyCountMapped : source.memaddrs (keys + 24#64)) (keyCountCell : source.memory (keys + 24#64) = .word keyCount)
    (keySeparate : message + 160#64 ≠ frame + 264#64)
    (keyCountSeparate : keys + 24#64 ≠ frame + 264#64)
    (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source countProgram =
      (some (.returned (.val (.word frame))), restore source "acc_n"
        (emptyLocalsHOLFinite (countedFinal source frame addressCount keyCount empty))) := by
  let called := WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} "acc_n" addressCount
  let first := countedFirst source frame addressCount
  let second := WitnessRadix.QueryBranch.bind {first with clock := first.clock - 1} "acc_n" keyCount
  let target := countedFinal source frame addressCount keyCount empty
  have calledFrame : called.locals.lookup (ofString "e") = some (.val (.word frame)) :=
    (bind_lookup_other _ "acc_n" "e" _ (by decide)).trans frameLocal
  have firstFrame : first.locals.lookup (ofString "e") = some (.val (.word frame)) := calledFrame
  have firstMessage : first.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "acc_n" "msg" _ (by decide)).trans messageLocal
  have secondFrame : second.locals.lookup (ofString "e") = some (.val (.word frame)) :=
    (bind_lookup_other _ "acc_n" "e" _ (by decide)).trans firstFrame
  have finalReady : ∀ field ∈ finalFields keyCount empty, field.value.Ready second "msg" message := by
    intro field member
    simp only [finalFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact bind_lookup_same _ _ _
    · exact emptyGlobal
    · exact emptyGlobal
    · trivial
  have finalMapped : ∀ field ∈ finalFields keyCount empty, second.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply frameMapped
    simp only [finalFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  have finalSeparate : ∀ reader ∈ finalFields keyCount empty, ∀ writer ∈ finalFields keyCount empty,
      reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer _
    simp only [finalFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  have returnRun : evaluateHOLFiniteState target (.return (localVar "e")) =
      (some (.returned (.val (.word frame))), emptyLocalsHOLFinite target) := by
    rw [evaluateHOLFiniteState_return]
    have targetFrame : target.locals.lookup (ofString "e") = some (.val (.word frame)) := secondFrame
    simp [localVar, evalHOLExact, toExact, targetFrame, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have finalRun := FieldStores.execute second "e" "msg" frame message (finalFields keyCount empty)
    secondFrame finalReady finalMapped finalSeparate (.return (localVar "e"))
  change evaluateHOLFiniteState second finalProgram = evaluateHOLFiniteState target (.return (localVar "e")) at finalRun
  rw [returnRun] at finalRun
  have keptKey : first.memory (message + 160#64) = .word keys := by
    change WitnessRadix.WordWrites.write _ _ _ = _
    rw [WitnessRadix.WordWrites.write_away]
    · exact keyCell
    · simpa [FieldStores.writes, firstCountFields] using keySeparate
  have keptKeyCount : first.memory (keys + 24#64) = .word keyCount := by
    change WitnessRadix.WordWrites.write _ _ _ = _
    rw [WitnessRadix.WordWrites.write_away]
    · exact keyCountCell
    · simpa [FieldStores.writes, firstCountFields] using keyCountSeparate
  have firstKeyMapped : first.memaddrs (message + 160#64) := keyMapped
  have secondArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [messageLoad 160] = some [.val (.word keys)] := by
    simp [evalListHOLFinite, evalHOLFinite, messageLoad, addConst, localVar, evalHOLExact,
      evalListHOLExact, toExact, firstMessage, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, isWfShapeExactHOL, firstKeyMapped, keptKey]
  have assignRun := TableCount.call_assign first "acc_n" [messageLoad 160] keys keyCount addressCount
    (bind_lookup_same _ _ _) secondArgs code keyCountMapped keptKeyCount
    (by change 1 ≤ source.clock - 1; omega)
  change evaluateHOLFiniteState first countAssign = (none, second) at assignRun
  have tailRun := WitnessRadix.StateSteps.next_sequence first second countAssign finalProgram assignRun
    (by change source.clock - 1 - 1 ≤ source.clock - 1; omega)
  rw [finalRun] at tailRun
  have firstReady : ∀ field ∈ firstCountFields addressCount, field.value.Ready called "msg" message := by
    intro field member
    simp only [firstCountFields, List.mem_cons, List.not_mem_nil, or_false] at member
    subst field
    exact bind_lookup_same _ _ _
  have firstMapped : ∀ field ∈ firstCountFields addressCount, called.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    simp only [firstCountFields, List.mem_cons, List.not_mem_nil, or_false] at member
    subst field
    exact frameMapped 264 (by simp)
  have firstRun := FieldStores.execute called "e" "msg" frame message (firstCountFields addressCount)
    calledFrame firstReady firstMapped (by intro reader member writer _; simp only [firstCountFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst reader; trivial)
    (.seq countAssign finalProgram)
  change evaluateHOLFiniteState called countContinuation = evaluateHOLFiniteState first (.seq countAssign finalProgram) at firstRun
  rw [tailRun] at firstRun
  have firstArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [messageLoad 152] = some [.val (.word addresses)] := by
    simp [evalListHOLFinite, evalHOLFinite, messageLoad, addConst, localVar, evalHOLExact,
      evalListHOLExact, toExact, messageLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, isWfShapeExactHOL, addressMapped, addressCell]
  have whole := TableCount.call_execute source "acc_n" [messageLoad 152] countContinuation
    addresses addressCount firstArgs code addressCountMapped addressCountCell (by omega)
  change evaluateHOLFiniteState source countProgram = _ at whole
  rw [firstRun] at whole
  exact whole

theorem counted_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame addressCount keyCount empty : BitVec 64) :
    regularBudget (countedFinal source frame addressCount keyCount empty).memory frame = regularBudget source.memory frame ∧
      (countedFinal source frame addressCount keyCount empty).clock = source.clock - 2 := by
  have kept (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :
      (countedFinal source frame addressCount keyCount empty).memory (frame + BitVec.ofNat 64 offset) =
        source.memory (frame + BitVec.ofNat 64 offset) := by
    apply count_memory_away
    intro other otherIn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member otherIn
    rcases member with rfl | rfl | rfl <;> rcases otherIn with rfl | rfl | rfl | rfl | rfl <;>
      simp [BitVec.add_right_inj]
  refine ⟨?_, ?_⟩
  · simp only [regularBudget, wordAt, kept 64 (by simp), kept 184 (by simp), kept 192 (by simp)]
  · change source.clock - 1 - 1 = source.clock - 2
    omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.count_memory_away
#print axioms InitECandidate.Solver.GasBudget.FrameNew.counts_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.counted_budget

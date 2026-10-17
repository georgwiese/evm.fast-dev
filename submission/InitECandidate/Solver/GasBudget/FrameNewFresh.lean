import InitECandidate.Solver.GasBudget.FrameNewInitialization

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def fresh (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch memory : BitVec 64) (words : MessageWords) :=
  initialized (zeroed source scratch memory) (Arenas.rounded .down scratch 280#64) memory scratch words
noncomputable def freshRestore (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch memory : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  closeScope source scratch memory
    (allocationRestore (zeroed source scratch memory) (Arenas.rounded .down scratch 280#64) scratch target)

theorem actual_fresh_prefix : body = program (initializedProgram afterGas) := by
  rw [actual_prefix, actual_initialization]

/-- Exact fresh-frame gas initialization in the unchanged constructor, through
both arena allocations and every store preceding compute_jumpdests. Input
message words are protected by physical separation from the new frame.
Entry code/cursor/domain/room/clock facts remain explicit; no zero-counter,
helper-result or intermediate memory-frame premise remains. -/
theorem fresh_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch memory message : BitVec 64) (words : MessageWords)
    (code : Code source)
    (memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (aligned : memory.toNat % 8 = 0) (firstRoom : memory.toNat + 280 ≤ scratch.toNat)
    (laterRoom : memory.toNat + 2055 ≤ (Arenas.rounded .down scratch 280#64).toNat)
    (mapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset))
    (messageMapped : ∀ offset ∈ messageOffsets, source.memaddrs (message + BitVec.ofNat 64 offset))
    (messageCells : ∀ offset ∈ messageOffsets,
      source.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset))
    (separate : ∀ readOffset ∈ messageOffsets, ∀ writeOffset < size,
      message + BitVec.ofNat 64 readOffset ≠ WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) writeOffset)
    (enough : 17 ≤ source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program (initializedProgram continuation)) =
      (let output := evaluateHOLFiniteState (fresh source scratch memory words) continuation
       (output.1, freshRestore source scratch memory output.2)) := by
  let frame := Arenas.rounded .down scratch 280#64
  let cleared := zeroed source scratch memory
  have eLocal : cleared.locals.lookup (ofString "e") = some (.val (.word frame)) :=
    (zeroed_fields source scratch memory).2.2.1
  have msgLocal : cleared.locals.lookup (ofString "msg") = some (.val (.word message)) := by
    change (allocated source scratch memory).locals.lookup (ofString "msg") = _
    unfold allocated
    rw [bind_lookup_other _ "e" "msg" _ (by decide)]
    change (markedMemory source scratch memory).locals.lookup (ofString "msg") = _
    unfold markedMemory
    rw [bind_lookup_other _ "mem_mark" "msg" _ (by decide)]
    change (markedScratch source scratch).locals.lookup (ofString "msg") = _
    exact (bind_lookup_other _ "stack_mark" "msg" _ (by decide)).trans messageLocal
  have savedScratch : cleared.locals.lookup (ofString "stack_mark") = some (.val (.word scratch)) := by
    change (allocated source scratch memory).locals.lookup (ofString "stack_mark") = _
    unfold allocated
    rw [bind_lookup_other _ "e" "stack_mark" _ (by decide)]
    change (markedMemory source scratch memory).locals.lookup (ofString "stack_mark") = _
    unfold markedMemory
    rw [bind_lookup_other _ "mem_mark" "stack_mark" _ (by decide)]
    exact bind_lookup_same _ _ _
  have savedMemory : cleared.locals.lookup (ofString "mem_mark") = some (.val (.word memory)) := by
    change (allocated source scratch memory).locals.lookup (ofString "mem_mark") = _
    unfold allocated
    rw [bind_lookup_other _ "e" "mem_mark" _ (by decide)]
    exact bind_lookup_same _ _ _
  have currentScratch : cleared.globals.lookup (ofString "scratch_ptr") = some (.val (.word frame)) := by
    simp [cleared, frame, zeroed, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have currentMemory : cleared.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) := by
    simpa [cleared, zeroed, allocated, markedMemory, markedScratch, Arenas.post, Arenas.pointerName,
      WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using memoryGlobal
  have frameMapped : ∀ offset ∈ stackOffsets ++ frameOffsets, cleared.memaddrs (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    apply mapped
    · simp only [stackOffsets, frameOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    · simp only [stackOffsets, frameOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
  have keptMessage : ∀ offset ∈ messageOffsets,
      cleared.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset) := by
    intro offset member
    rw [zeroed_away]
    · exact messageCells offset member
    · exact separate offset member
  have separated : ∀ readOffset ∈ messageOffsets, ∀ writeOffset ∈ stackOffsets ++ frameOffsets,
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset := by
    intro readOffset readIn writeOffset writeIn
    apply separate readOffset readIn
    simp only [stackOffsets, frameOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at writeIn
    rcases writeIn with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
  have clearedClock : cleared.clock = source.clock - 15 := (zeroed_fields source scratch memory).2.1
  have initRun := initialize_execute cleared frame memory scratch message words code.scratch memoryCode
    eLocal msgLocal savedScratch savedMemory currentScratch currentMemory aligned laterRoom frameMapped
    messageMapped keptMessage separated (by rw [clearedClock]; omega) continuation
  change evaluateHOLFiniteState cleared (initializedProgram continuation) =
    (let output := evaluateHOLFiniteState (fresh source scratch memory words) continuation
     (output.1, allocationRestore cleared frame scratch output.2)) at initRun
  have prefixRun := execute_zero source scratch memory code scratchGlobal memoryGlobal aligned firstRoom mapped
    (by omega) (initializedProgram continuation)
  rw [initRun] at prefixRun
  exact prefixRun

/-- The actual cleared words derive the two zero counters required by the
message-store ledger theorem. The constructed frame's regular budget is
exactly incoming MSG_GAS, and the prefix consumes 17 source clocks. -/
theorem fresh_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch memory : BitVec 64) (words : MessageWords) :
    regularBudget (fresh source scratch memory words).memory (Arenas.rounded .down scratch 280#64) = words.gas.toNat ∧
      (fresh source scratch memory words).clock = source.clock - 17 := by
  have used := zeroed_cell source scratch memory 23 (by decide)
  have spill := zeroed_cell source scratch memory 24 (by decide)
  have budget := initialized_regular (zeroed source scratch memory) (Arenas.rounded .down scratch 280#64)
    memory scratch words used spill
  refine ⟨budget, ?_⟩
  change (initialized _ _ _ _ _).clock = _
  rw [initialized_clock, (zeroed_fields source scratch memory).2.1]
  omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_fresh_prefix
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_budget

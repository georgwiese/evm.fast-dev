import InitECandidate.Solver.GasBudget.FrameNewAllocation

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def initializedProgram (continuation : ProgHOL 64) : ProgHOL 64 := allocationProgram (gasProgram continuation)
noncomputable def initialized (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame memory mark : BitVec 64) (words : MessageWords) :=
  {memoryAllocated source frame memory mark with memory := (WitnessRadix.WordWrites.write
    (memoryAllocated source frame memory mark).memory (FieldStores.writes frame (fields memory memory words)))}

theorem actual_initialization : afterZero = initializedProgram afterGas := by
  rw [actual_allocations, actual_gas_stores]
  rfl

/-- Composition of the actual two allocations, stack metadata, and all seven
message/frame stores. Earlier message words and both zero counters are carried
through every real intervening operation; helper results are derived. -/
theorem initialize_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame memory mark message : BitVec 64) (words : MessageWords)
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one))
    (frameLocal : source.locals.lookup (ofString "e") = some (.val (.word frame)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (stackMark : source.locals.lookup (ofString "stack_mark") = some (.val (.word mark)))
    (memoryMark : source.locals.lookup (ofString "mem_mark") = some (.val (.word memory)))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word frame)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (aligned : memory.toNat % 8 = 0) (room : memory.toNat + 2055 ≤ frame.toNat)
    (frameMapped : ∀ offset ∈ stackOffsets ++ frameOffsets, source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageMapped : ∀ offset ∈ messageOffsets, source.memaddrs (message + BitVec.ofNat 64 offset))
    (messageCells : ∀ offset ∈ messageOffsets,
      source.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset))
    (separate : ∀ readOffset ∈ messageOffsets, ∀ writeOffset ∈ stackOffsets ++ frameOffsets,
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset)
    (enough : 2 ≤ source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (initializedProgram continuation) =
      (let output := evaluateHOLFiniteState (initialized source frame memory mark words) continuation
       (output.1, allocationRestore source frame mark output.2)) := by
  let allocated := memoryAllocated source frame memory mark
  have eLocal : allocated.locals.lookup (ofString "e") = some (.val (.word frame)) :=
    (allocation_other source frame memory mark "e" (by decide) (by decide)).trans frameLocal
  have msgLocal : allocated.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (allocation_other source frame memory mark "msg" (by decide) (by decide)).trans messageLocal
  have markLocal : allocated.locals.lookup (ofString "mem_mark") = some (.val (.word memory)) :=
    (allocation_other source frame memory mark "mem_mark" (by decide) (by decide)).trans memoryMark
  have memLocal : allocated.locals.lookup (ofString "mem") = some (.val (.word memory)) :=
    (allocation_fields source frame memory mark).2.2.2.2
  have keptMessage : ∀ offset ∈ messageOffsets,
      allocated.memory (message + BitVec.ofNat 64 offset) = .word (words.atOffset offset) := by
    intro offset member
    rw [allocation_memory_away]
    · exact messageCells offset member
    · simp only [FieldStores.writes, stackFields, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨separate offset member 208 (by simp [stackOffsets]),
        separate offset member 8 (by simp [stackOffsets]),
        separate offset member 232 (by simp [stackOffsets])⟩
  have frameMappedA : ∀ offset ∈ frameOffsets, allocated.memaddrs (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    exact frameMapped offset (List.mem_append_right _ member)
  have separated : ∀ readOffset ∈ messageOffsets, ∀ writeOffset ∈ frameOffsets,
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset := by
    intro readOffset readIn writeOffset writeIn
    exact separate readOffset readIn writeOffset (List.mem_append_right _ writeIn)
  have gasRun := gas_stores_execute allocated frame message memory memory words eLocal msgLocal markLocal memLocal
    frameMappedA messageMapped keptMessage separated continuation
  change evaluateHOLFiniteState allocated (gasProgram continuation) =
    evaluateHOLFiniteState (initialized source frame memory mark words) continuation at gasRun
  have allocationRun := allocate_execute source frame memory mark scratchCode memoryCode frameLocal stackMark
    scratchGlobal memoryGlobal aligned room
    (by intro offset member; exact frameMapped offset (List.mem_append_left _ member)) enough (gasProgram continuation)
  change evaluateHOLFiniteState source (initializedProgram continuation) = _ at allocationRun
  rw [gasRun] at allocationRun
  exact allocationRun

theorem initialized_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame memory mark : BitVec 64) (words : MessageWords) :
    (initialized source frame memory mark words).clock = source.clock - 2 :=
  (allocation_fields source frame memory mark).1

/-- The initialized frame's regular ledger equals precisely the message gas,
provided its two real counters were zero at entry to the allocation suffix. -/
theorem initialized_regular (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame memory mark : BitVec 64) (words : MessageWords)
    (used : source.memory (frame + 184#64) = .word 0#64)
    (spill : source.memory (frame + 192#64) = .word 0#64) :
    regularBudget (initialized source frame memory mark words).memory frame = words.gas.toNat := by
  have keptUsed : (memoryAllocated source frame memory mark).memory (frame + 184#64) = .word 0#64 := by
    rw [allocation_memory_away]
    · exact used
    · simp [FieldStores.writes, stackFields, BitVec.add_right_inj]
  have keptSpill : (memoryAllocated source frame memory mark).memory (frame + 192#64) = .word 0#64 := by
    rw [allocation_memory_away]
    · exact spill
    · simp [FieldStores.writes, stackFields, BitVec.add_right_inj]
  exact initialized_budget _ frame memory memory words keptUsed keptSpill

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_initialization
#print axioms InitECandidate.Solver.GasBudget.FrameNew.initialize_execute
#print axioms InitECandidate.Solver.GasBudget.FrameNew.initialized_clock
#print axioms InitECandidate.Solver.GasBudget.FrameNew.initialized_regular

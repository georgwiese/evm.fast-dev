import InitECandidate.Solver.GasBudget.FrameNewFields

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stackOffsets : List Nat := [208, 8, 232]
def stackFields (mark stack : BitVec 64) : List FieldStores.Field :=
  [⟨208, .saved "stack_mark" mark⟩, ⟨8, .saved "stk" stack⟩, ⟨232, .literal 32#64⟩]
def stackAmount : ExpHOL 64 := .panop .mul [.const 32#64, .const 32#64]
def allocationProgram (continuation : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "stk") .one (ofString "scratch_alloc") [stackAmount]
    (FieldStores.program "e" "msg" (stackFields 0#64 0#64)
      (.decCall (ofString "mem") .one (ofString "frame_mem_alloc") [.const 1024#64] continuation))

set_option maxRecDepth 10000 in
theorem actual_allocations : afterZero = allocationProgram gasSite := by
  simp only [afterZero, gasSite, body, Guest.guestFn_frame_new, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, allocationProgram, stackAmount,
    FieldStores.program, FieldStores.address, FieldStores.Value.expression, stackFields, localVar, addConst]

noncomputable def stackAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) :=
  bind (Arenas.post {source with clock := source.clock - 1} .down frame 1024#64) "stk" (Arenas.rounded .down frame 1024#64)
noncomputable def stackInitialized (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame mark : BitVec 64) :=
  {stackAllocated source frame with memory := (WitnessRadix.WordWrites.write source.memory
    (FieldStores.writes frame (stackFields mark (Arenas.rounded .down frame 1024#64))))}
noncomputable def memoryAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark : BitVec 64) :=
  bind (Arenas.post {stackInitialized source frame mark with clock := (stackInitialized source frame mark).clock - 1}
    .up memory 1024#64) "mem" memory
noncomputable def allocationRestore (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame mark : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "stk" (restore (stackInitialized source frame mark) "mem" target)

/-- Both real allocations and intervening stack-field stores. Natural arena
room proves each guard. No allocation result or memory frame is assumed. -/
theorem allocate_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark : BitVec 64)
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one))
    (frameLocal : source.locals.lookup (ofString "e") = some (.val (.word frame)))
    (markLocal : source.locals.lookup (ofString "stack_mark") = some (.val (.word mark)))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word frame)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (aligned : memory.toNat % 8 = 0) (room : memory.toNat + 2055 ≤ frame.toNat)
    (mapped : ∀ offset ∈ stackOffsets, source.memaddrs (frame + BitVec.ofNat 64 offset))
    (enough : 2 ≤ source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (allocationProgram continuation) =
      (let output := evaluateHOLFiniteState (memoryAllocated source frame memory mark) continuation
       (output.1, allocationRestore source frame mark output.2)) := by
  classical
  have scratchRoom : memory.toNat + (1024#64 : BitVec 64).toNat ≤ frame.toNat := by change memory.toNat + 1024 ≤ frame.toNat; omega
  have geometry := Arenas.downward_guards frame memory 1024#64 aligned scratchRoom
  have number := Arenas.rounded_down_nat frame 1024#64
    (show (1024#64 : BitVec 64) ≤ frame from by change 1024 ≤ frame.toNat; omega)
  have memoryRoom : memory.toNat + (1024#64 : BitVec 64).toNat ≤ (Arenas.rounded .down frame 1024#64).toNat := by
    change memory.toNat + 1024 ≤ _
    rw [number]
    change memory.toNat + 1024 ≤ (frame.toNat - 1024) / 8 * 8
    omega
  have argsStack : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) [stackAmount] = some [.val (.word 1024#64)] := by
    simp [stackAmount, evalListHOLFinite, evalListHOLExact, evalHOLExact, panOpHOL, valueIsWord, valueWord]
  let memoryCall := ProgHOL.decCall (ofString "mem") .one (ofString "frame_mem_alloc") [.const 1024#64] continuation
  have frameS : (stackAllocated source frame).locals.lookup (ofString "e") = some (.val (.word frame)) :=
    (bind_lookup_other _ "stk" "e" _ (by decide)).trans frameLocal
  have markS : (stackAllocated source frame).locals.lookup (ofString "stack_mark") = some (.val (.word mark)) :=
    (bind_lookup_other _ "stk" "stack_mark" _ (by decide)).trans markLocal
  have stackS : (stackAllocated source frame).locals.lookup (ofString "stk") =
      some (.val (.word (Arenas.rounded .down frame 1024#64))) := bind_lookup_same _ _ _
  have reads : ∀ field ∈ stackFields mark (Arenas.rounded .down frame 1024#64),
      field.value.Ready (stackAllocated source frame) "msg" 0#64 := by
    intro field member
    simp only [stackFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact markS
    · exact stackS
    · trivial
  have storesMapped : ∀ field ∈ stackFields mark (Arenas.rounded .down frame 1024#64),
      (stackAllocated source frame).memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    simp only [stackFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [stackOffsets]
  have separated : ∀ reader ∈ stackFields mark (Arenas.rounded .down frame 1024#64),
      ∀ writer ∈ stackFields mark (Arenas.rounded .down frame 1024#64),
      reader.value.Avoid 0#64 (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader readerIn writer writerIn
    simp only [stackFields, List.mem_cons, List.not_mem_nil, or_false] at readerIn
    rcases readerIn with rfl | rfl | rfl <;> trivial
  have storesRun := FieldStores.execute (stackAllocated source frame) "e" "msg" frame 0#64
    (stackFields mark (Arenas.rounded .down frame 1024#64)) frameS reads storesMapped separated memoryCall
  change evaluateHOLFiniteState (stackAllocated source frame)
      (FieldStores.program "e" "msg" (stackFields 0#64 0#64) memoryCall) =
    evaluateHOLFiniteState (stackInitialized source frame mark) memoryCall at storesRun
  have argsMemory : evalListHOLFinite (stackInitialized source frame mark)
      (h := fun address => Classical.propDecidable ((stackInitialized source frame mark).memaddrs address))
      [.const 1024#64] = some [.val (.word 1024#64)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have scratchUpdated : (stackInitialized source frame mark).globals.lookup (ofString "scratch_ptr") =
      some (.val (.word (Arenas.rounded .down frame 1024#64))) := by
    simp [stackInitialized, stackAllocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE]
  have memoryKept : (stackInitialized source frame mark).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) := by
    simpa [stackInitialized, stackAllocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE, ofString] using memoryGlobal
  have memoryRun := Arenas.call_execute (stackInitialized source frame mark) .up "mem" [.const 1024#64] continuation
    memory (Arenas.rounded .down frame 1024#64) 1024#64 argsMemory memoryCode memoryKept scratchUpdated
    geometry.2.2.2.2.2 memoryRoom (by change 1 ≤ source.clock - 1; omega)
  change evaluateHOLFiniteState (stackInitialized source frame mark) memoryCall =
    (let output := evaluateHOLFiniteState (memoryAllocated source frame memory mark) continuation
     (output.1, restore (stackInitialized source frame mark) "mem" output.2)) at memoryRun
  rw [memoryRun] at storesRun
  have stackRun := Arenas.call_execute source .down "stk" [stackAmount]
    (FieldStores.program "e" "msg" (stackFields 0#64 0#64) memoryCall)
    frame memory 1024#64 argsStack scratchCode scratchGlobal memoryGlobal aligned scratchRoom (by omega)
  change evaluateHOLFiniteState source (allocationProgram continuation) =
    (let output := evaluateHOLFiniteState (stackAllocated source frame)
      (FieldStores.program "e" "msg" (stackFields 0#64 0#64) memoryCall)
     (output.1, restore source "stk" output.2)) at stackRun
  rw [storesRun] at stackRun
  exact stackRun

theorem allocation_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark : BitVec 64)
    (name : String) (notMemory : ofString "mem" ≠ ofString name) (notStack : ofString "stk" ≠ ofString name) :
    (memoryAllocated source frame memory mark).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  unfold memoryAllocated
  rw [bind_lookup_other _ "mem" name _ notMemory]
  change (stackAllocated source frame).locals.lookup (ofString name) = source.locals.lookup (ofString name)
  exact bind_lookup_other _ "stk" name _ notStack

theorem allocation_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark query : BitVec 64)
    (away : query ∉ (FieldStores.writes frame (stackFields mark (Arenas.rounded .down frame 1024#64))).map Prod.fst) :
    (memoryAllocated source frame memory mark).memory query = source.memory query :=
  WitnessRadix.WordWrites.write_away source.memory _ query away

/-- Arena allocation and the three stack metadata stores preserve all three
regular-budget cells. The message gas has not yet been copied in. -/
theorem allocation_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark : BitVec 64) :
    regularBudget (memoryAllocated source frame memory mark).memory frame = regularBudget source.memory frame := by
  have same : ∀ offset ∈ ([64, 184, 192] : List Nat),
      (memoryAllocated source frame memory mark).memory (frame + BitVec.ofNat 64 offset) =
        source.memory (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    apply allocation_memory_away
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [FieldStores.writes, stackFields, BitVec.add_right_inj]
  simp only [regularBudget, wordAt, same 64 (by simp), same 184 (by simp), same 192 (by simp)]

theorem allocation_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame memory mark : BitVec 64) :
    (memoryAllocated source frame memory mark).clock = source.clock - 2 ∧
      (memoryAllocated source frame memory mark).code = source.code ∧
      (memoryAllocated source frame memory mark).memaddrs = source.memaddrs ∧
      (memoryAllocated source frame memory mark).ffi = source.ffi ∧
      (memoryAllocated source frame memory mark).locals.lookup (ofString "mem") = some (.val (.word memory)) := by
  refine ⟨?_, rfl, rfl, rfl, bind_lookup_same _ _ _⟩
  change source.clock - 1 - 1 = source.clock - 2
  omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_allocations
#print axioms InitECandidate.Solver.GasBudget.FrameNew.allocate_execute

#print axioms InitECandidate.Solver.GasBudget.FrameNew.allocation_other
#print axioms InitECandidate.Solver.GasBudget.FrameNew.allocation_memory_away
#print axioms InitECandidate.Solver.GasBudget.FrameNew.allocation_budget
#print axioms InitECandidate.Solver.GasBudget.FrameNew.allocation_fields

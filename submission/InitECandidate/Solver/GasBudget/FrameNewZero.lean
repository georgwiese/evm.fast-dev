import InitECandidate.Solver.GasBudget.FrameNewProgram

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual frame constructor's two marks, allocation and full 280-byte
clear. All helper executions are proved from code/cursor/room premises; no
memory effects or helper return values are assumed. -/
theorem execute_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (code : Code source)
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (aligned : memory.toNat % 8 = 0) (room : memory.toNat + 280 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset))
    (enough : 15 ≤ source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program continuation) =
      (let output := evaluateHOLFiniteState (zeroed source scratch memory) continuation
       (output.1, closeScope source scratch memory output.2)) := by
  classical
  let zeroRest : ProgHOL 64 := .seq clear continuation
  let allocateRest := ProgHOL.decCall (ofString "e") .one (ofString "scratch_alloc") [.const 280#64] zeroRest
  let memoryRest := ProgHOL.decCall (ofString "mem_mark") .one (ofString "frame_mem_mark") [] allocateRest
  have argsAlloc : evalListHOLFinite (markedMemory source scratch memory)
      (h := fun address => Classical.propDecidable ((markedMemory source scratch memory).memaddrs address))
      [.const 280#64] = some [.val (.word 280#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have calledAlloc := Arenas.call_execute (markedMemory source scratch memory) .down "e" [.const 280#64] zeroRest
    scratch memory 280#64 argsAlloc code.scratch scratchGlobal memoryGlobal aligned room
    (by change 1 ≤ source.clock - 1 - 1; omega)
  change evaluateHOLFiniteState (markedMemory source scratch memory) allocateRest =
    (let output := evaluateHOLFiniteState (allocated source scratch memory) zeroRest
     (output.1, restore (markedMemory source scratch memory) "e" output.2)) at calledAlloc
  have eLocal : (allocated source scratch memory).locals.lookup (ofString "e") =
      some (.val (.word (Arenas.rounded .down scratch 280#64))) := bind_lookup_same _ _ _
  have argsZero : evalListHOLFinite (allocated source scratch memory)
      (h := fun address => Classical.propDecidable ((allocated source scratch memory).memaddrs address))
      [localVar "e", .const 280#64] = some (WitnessRadix.Zero.values (Arenas.rounded .down scratch 280#64) size) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, eLocal, WitnessRadix.Zero.values, size]
  have geometry := Arenas.downward_guards scratch memory 280#64 aligned room
  have calledZero := WitnessRadix.Zero.call_execute (allocated source scratch memory)
    [localVar "e", .const 280#64] (Arenas.rounded .down scratch 280#64) size argsZero code.zero
    (by decide) (by decide) geometry.2.2.2.2.2 mapped
    (by change 12 ≤ source.clock - 1 - 1 - 1; omega)
  change evaluateHOLFiniteState (allocated source scratch memory) clear = (none, zeroed source scratch memory) at calledZero
  have zeroNext := WitnessRadix.StateSteps.next_sequence (allocated source scratch memory) (zeroed source scratch memory)
    clear continuation calledZero (by change (allocated source scratch memory).clock - _ ≤ (allocated source scratch memory).clock; omega)
  change evaluateHOLFiniteState (allocated source scratch memory) zeroRest =
    evaluateHOLFiniteState (zeroed source scratch memory) continuation at zeroNext
  rw [zeroNext] at calledAlloc
  have calledMemory := Arenas.mark_call (markedScratch source scratch) .up "mem_mark" memory allocateRest
    code.memoryMark memoryGlobal (by change 1 ≤ source.clock - 1; omega)
  change evaluateHOLFiniteState (markedScratch source scratch) memoryRest =
    (let output := evaluateHOLFiniteState (markedMemory source scratch memory) allocateRest
     (output.1, restore (markedScratch source scratch) "mem_mark" output.2)) at calledMemory
  rw [calledAlloc] at calledMemory
  have calledScratch := Arenas.mark_call source .down "stack_mark" scratch memoryRest
    code.scratchMark scratchGlobal (by omega)
  change evaluateHOLFiniteState source (program continuation) =
    (let output := evaluateHOLFiniteState (markedScratch source scratch) memoryRest
     (output.1, restore source "stack_mark" output.2)) at calledScratch
  rw [calledMemory] at calledScratch
  exact calledScratch

/-- Every complete field of the actual freshly cleared frame is zero. -/
theorem zeroed_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (slot : Nat) (inside : 8 * (slot + 1) ≤ size) :
    (zeroed source scratch memory).memory (Arenas.rounded .down scratch 280#64 + BitVec.ofNat 64 (8 * slot)) = .word 0#64 :=
  MutableTable.ZeroWords.final_cell source.memory _ size slot inside

/-- The original frame's liquid/used/spill cells are all zero before the
message gas is copied in. The exact checked prefix consumes 15 source clocks. -/
theorem zeroed_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64) :
    regularBudget (zeroed source scratch memory).memory (Arenas.rounded .down scratch 280#64) = 0 ∧
      (zeroed source scratch memory).clock = source.clock - 15 ∧
      (zeroed source scratch memory).locals.lookup (ofString "e") =
        some (.val (.word (Arenas.rounded .down scratch 280#64))) ∧
      (zeroed source scratch memory).code = source.code ∧
      (zeroed source scratch memory).ffi = source.ffi := by
  have gas := zeroed_cell source scratch memory 8 (by decide)
  have used := zeroed_cell source scratch memory 23 (by decide)
  have spill := zeroed_cell source scratch memory 24 (by decide)
  refine ⟨?_, ?_, bind_lookup_same _ _ _, rfl, rfl⟩
  · simp only [regularBudget, wordAt, gas, used, spill, WitnessRadix.MemoryBytes.wordBits,
      BitVec.toNat_zero, Nat.zero_add]
  · change source.clock - 1 - 1 - 1 - 12 = source.clock - 15
    omega

/-- The clear preserves every word outside its own newly allocated frame. -/
theorem zeroed_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory query : BitVec 64)
    (away : ∀ offset < size, query ≠ WitnessRadix.byteAddress (Arenas.rounded .down scratch 280#64) offset) :
    (zeroed source scratch memory).memory query = source.memory query :=
  WitnessRadix.Zero.final_memory_away source.memory _ query size away

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.execute_zero

#print axioms InitECandidate.Solver.GasBudget.FrameNew.zeroed_cell
#print axioms InitECandidate.Solver.GasBudget.FrameNew.zeroed_fields
#print axioms InitECandidate.Solver.GasBudget.FrameNew.zeroed_away

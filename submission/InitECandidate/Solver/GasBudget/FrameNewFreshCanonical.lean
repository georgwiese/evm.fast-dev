import InitECandidate.Solver.GasBudget.FrameNewMapped

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem fresh_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower : BitVec 64) (words : MessageWords) :
    (fresh source scratch lower words).globals =
      (source.globals.update (ofString "scratch_ptr", .val (.word (stackPointer scratch)))).update
        (ofString "frame_mem_ptr", .val (.word (memoryPointer lower))) := by
  have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word (framePointer scratch)))).update
      (ofString "scratch_ptr", .val (.word (stackPointer scratch))) =
      source.globals.update (ofString "scratch_ptr", .val (.word (stackPointer scratch))) := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
  change ((source.globals.update (ofString "scratch_ptr", .val (.word (framePointer scratch)))).update
    (ofString "scratch_ptr", .val (.word (stackPointer scratch)))).update
      (ofString "frame_mem_ptr", .val (.word (memoryPointer lower))) = _
  rw [overwrite]

theorem fresh_final_canonical (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower : BitVec 64) (words : MessageWords) (finalScratch : BitVec 64) (memory : Memory) (clock : Nat) :
    emptyLocalsHOLFinite {fresh source scratch lower words with
      globals := (fresh source scratch lower words).globals.update (ofString "scratch_ptr", .val (.word finalScratch))
      memory := memory
      clock := clock} =
    emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word finalScratch))
      memory := memory
      clock := clock} := by
  have globals : ((source.globals.update (ofString "scratch_ptr", .val (.word (stackPointer scratch)))).update
      (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
      (ofString "scratch_ptr", .val (.word finalScratch)) =
      (source.globals.update (ofString "frame_mem_ptr", .val (.word (memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word finalScratch)) := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases scratchEq : ofString "scratch_ptr" = query <;>
      by_cases memoryEq : ofString "frame_mem_ptr" = query <;>
        simp [HolFiniteMapExact.update, FUPDATE, scratchEq, memoryEq]
  change emptyLocalsHOLFinite {source with
    globals := (fresh source scratch lower words).globals.update (ofString "scratch_ptr", .val (.word finalScratch))
    memory := memory
    clock := clock} = _
  rw [fresh_globals, globals]

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_globals
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_final_canonical

import InitECandidate.Solver.ScratchTable.Frames
import InitECandidate.Solver.Arenas.Region

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Full unchanged 20-byte/capacity4 scratch-table constructor used for frame
DELETE sets. All six allocations, nine header stores, actual four-byte clear,
return and lexical scopes compose. The body consumes exactly11source clocks;
its272byte scratch plan preserves every word above the incoming cursor. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 20#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64)))
    (scratchAligned : scratch.toNat % 8 = 0) (memoryAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + 272 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset))
    (usedMapped : source.memaddrs (cursor scratch 208))
    (enough : 11 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (cursor scratch 72)))), target) ∧
      target.memory = (finalState source scratch).memory ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "scratch_ptr", .val (.word (cursor scratch 272)))
        memory := target.memory
        clock := source.clock - 11} ∧
      ∀ query : BitVec 64, Arenas.Outside memory scratch query → target.memory query = source.memory query := by
  have first := initial_executes source scratch memory code scratchGlobal memoryGlobal keyLocal capLocal scratchAligned memoryAligned
    (by omega) mapped (by omega)
  obtain ⟨middleRestore, middle⟩ := middle_executes source scratch memory code memoryGlobal capLocal scratchAligned memoryAligned room mapped (by omega)
  obtain ⟨finishRestore, finish⟩ := finish_executes source scratch memory code zeroCode memoryGlobal capLocal scratchAligned memoryAligned room mapped usedMapped enough
  have setup := first.append (middle.append finish)
  have returned : evaluateHOLFiniteState (finalState source scratch) WitnessRadix.TableNew.returnTable =
      (some (.returned (.val (.word (cursor scratch 72)))), emptyLocalsHOLFinite (finalState source scratch)) := by
    have tableLocal := (final_locals source scratch capLocal).table
    simp [WitnessRadix.TableNew.returnTable, evaluateHOLFiniteState_return, localVar, evalHOLExact,
      toExact, tableLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have actual := Arenas.Prefix.execute setup WitnessRadix.TableNew.returnTable
  rw [returned] at actual
  let target := restore source "t" (restore (tableState source scratch) "stride"
    (middleRestore (finishRestore (emptyLocalsHOLFinite (finalState source scratch)))))
  have restoreFrame := Arenas.Prefix.restoration_frame setup (emptyLocalsHOLFinite (finalState source scratch))
  change emptyLocalsHOLFinite target = emptyLocalsHOLFinite (finalState source scratch) at restoreFrame
  have memoryEq : target.memory = (finalState source scratch).memory := congrArg (fun state => state.memory) restoreFrame
  refine ⟨target, ?_, memoryEq, ?_, ?_⟩
  · rw [body_shape]
    exact actual
  · simpa only [memoryEq] using restoreFrame.trans (final_frame source scratch)
  · intro query outsideArena
    rw [memoryEq]
    apply final_memory_outside source scratch query scratchAligned (by omega)
    have number : (cursor scratch 272).toNat = scratch.toNat - 272 := Arenas.cursor_number scratch 272 (by omega)
    rcases outsideArena with below | above
    · left
      omega
    · exact Or.inr above

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.execute

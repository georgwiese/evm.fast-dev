import InitECandidate.Solver.GasBudget.RunFramesRevert
import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminalScopes
import InitECandidate.Solver.GasBudget.RunFramesActiveBody

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Full actual active REVERT iteration, including lexical scopes. -/
theorem active_revert (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base current capacity pointer scratch sp running pc codeLength : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (header : ActiveHeader source view.frame view.continuation running pc codeLength)
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 253#64)))
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (reservoirOwned : Arenas.Outside base scratch (view.message + 48#64))
    (reservoirApart : ∀ offset ∈ ([16, 32, 40, 64, 184, 120, 128] : List Nat), view.message + 48#64 ≠ view.frame + BitVec.ofNat 64 offset)
    (continuationApart : ∀ offset ∈ ([24, 32, 40] : List Nat), view.frame + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    ∃ length nextCapacity nextPointer,
      MemoryTerminal source post view.frame view.continuation base scratch current capacity length nextCapacity nextPointer 34 := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc codeLength header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let phaseView := view.after_prefix setup
  obtain ⟨length, nextCapacity, nextPointer, terminal⟩ := caught_revert phase handled phaseView base current capacity pointer scratch sp
    (memoryView.after_erase rfl) covered shapes read spMapped spCell reservoirOwned reservoirApart continuationApart caughtRun
  exact ⟨length, nextCapacity, nextPointer, terminal.of_scopes rfl postScope⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_revert

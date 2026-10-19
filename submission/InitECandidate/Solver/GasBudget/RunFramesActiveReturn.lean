import InitECandidate.Solver.GasBudget.RunFramesReturn
import InitECandidate.Solver.GasBudget.RunFramesActiveBody

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Full actual active RETURN iteration, with both real error handlers and
the normal halted frame represented by the same completion contract. -/
theorem active_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base current capacity pointer scratch sp running pc codeLength : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (header : ActiveHeader source view.frame view.continuation running pc codeLength)
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 243#64)))
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (continuationOwned : Arenas.Outside base scratch (view.continuation + 32#64))
    (continuationApart : ∀ offset ∈ ([16, 24, 32, 40, 64, 184, 120, 128, 104] : List Nat),
      view.continuation + 32#64 ≠ view.frame + BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    ∃ length nextCapacity nextPointer,
      MemoryCompletion source post view.frame view.continuation base scratch current capacity length nextCapacity nextPointer 34 := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc codeLength header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let phaseView := view.after_prefix setup
  obtain ⟨length, nextCapacity, nextPointer, completed⟩ := caught_return phase handled phaseView base current capacity pointer scratch sp
    (memoryView.after_erase rfl) covered shapes read spMapped spCell header.2.2.2.2.1 header.2.2.2.1 continuationOwned continuationApart caughtRun
  exact ⟨length, nextCapacity, nextPointer, completed.of_scopes rfl postScope⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_return

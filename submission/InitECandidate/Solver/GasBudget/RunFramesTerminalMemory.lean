import InitECandidate.Solver.GasBudget.FrameExceptionHandlerMemory

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Physical effect of a pre-charge terminal path: only the active stack
pointer, handler fields and continuation marker can change. -/
structure TerminalMemory (before after : Memory) (frame cont : BitVec 64) : Prop where
  used : (wordAt before (frame + 184#64)).toNat ≤ (wordAt after (frame + 184#64)).toNat
  outside : ∀ address, address ≠ frame + 16#64 →
    (∀ offset ∈ FrameException.writeOffsets, address ≠ frame + BitVec.ofNat 64 offset) →
    address ≠ cont + 32#64 → after address = before address

theorem terminal_memory_after_prefix (source exceptionPost saved post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (err : BitVec 64) (paid : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : StackPop.PrefixEffect source exceptionPost view.frame paid)
    (normal : evaluateHOLFiniteState (bind {exceptionPost with locals := saved.locals} "err" err) opcodeHandler = (none, post)) :
    TerminalMemory source.memory post.memory view.frame view.continuation := by
  let handler := bind {exceptionPost with locals := saved.locals} "err" err
  have handlerEffect : StackPop.PrefixEffect source handler view.frame paid := effect.of_emptyLocals rfl
  let current := view.after_prefix handlerEffect
  have code := congrArg PanSemStateFiniteExact.code handlerEffect.fields
  change handler.code = source.code at code
  have installedCurrent : Input.OriginalCode.Installed handler.code := by rw [code]; exact installed
  have errLocal : handler.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "err") = some (.val (.word err)) := bind_lookup_same _ _ _
  have monotone := FrameException.handler_used_monotone handler post current err installedCurrent errLocal normal
  have memoryEq := FrameException.handler_memory handler post current err installedCurrent errLocal normal
  refine ⟨?_, ?_⟩
  · change (wordAt source.memory (view.frame + 184#64)).toNat ≤ (wordAt post.memory (view.frame + 184#64)).toNat
    change (wordAt handler.memory (view.frame + 184#64)).toNat ≤ (wordAt post.memory (view.frame + 184#64)).toNat at monotone
    simpa only [wordAt, handlerEffect.used] using monotone
  · intro address notSP notFrame notCont
    rw [memoryEq]
    exact (FrameException.memory_after_away handler.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir address notFrame notCont).trans
      (handlerEffect.outside address notSP)

theorem TerminalMemory.sums {before after : Memory} {frame cont : BitVec 64}
    (effect : TerminalMemory before after frame cont) (ancestors : List (BitVec 64))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 16#64 ∧
      (∀ field ∈ FrameException.writeOffsets, ancestor + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ cont + 32#64)
    (parentBudget : regularBudget after frame = regularBudget before frame) :
    FrameSums.budget after (frame :: ancestors) = FrameSums.budget before (frame :: ancestors) ∧
    FrameSums.used before (frame :: ancestors) ≤ FrameSums.used after (frame :: ancestors) := by
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      after (ancestor + BitVec.ofNat 64 offset) = before (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    obtain ⟨notSP, notFrame, notCont⟩ := apart ancestor member offset inside
    exact effect.outside _ notSP notFrame notCont
  have budget := FrameSums.budget_congr before after ancestors cells
  have used := FrameSums.used_congr before after ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  constructor
  · change regularBudget after frame + FrameSums.budget after ancestors = regularBudget before frame + FrameSums.budget before ancestors
    rw [parentBudget, budget]
  · change (wordAt before (frame + 184#64)).toNat + FrameSums.used before ancestors ≤
      (wordAt after (frame + 184#64)).toNat + FrameSums.used after ancestors
    rw [used]
    exact Nat.add_le_add_right effect.used _

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.terminal_memory_after_prefix
#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalMemory.sums

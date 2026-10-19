import InitECandidate.Solver.GasBudget.FrameExceptionPrefixHandler
import InitECandidate.Solver.GasBudget.RunFramesTerminalFrame

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The terminal physical effect includes the actual CALL address scratch. -/
structure FrameTerminalMemory (before after : Memory) (frame cont : BitVec 64) : Prop where
  used : (wordAt before (frame + 184#64)).toNat ≤ (wordAt after (frame + 184#64)).toNat
  outside : ∀ address, address ≠ frame + 16#64 → MemoryWriter.BytesAway (frame + 240#64) address 20 →
    (∀ offset ∈ FrameException.writeOffsets, address ≠ frame + BitVec.ofNat 64 offset) →
    address ≠ cont + 32#64 → after address = before address

structure FrameTerminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame cont : BitVec 64) (ceiling : Nat) : Prop where
  completion : TerminalFrame source post frame cont ceiling
  memoryEffect : FrameTerminalMemory source.memory post.memory frame cont

theorem frame_terminal_after_prefix (source exceptionPost post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (err : BitVec 64) (paid ceiling : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : FramePrefixEffect source exceptionPost view.frame paid)
    (aligned : view.frame.toNat % 8 = 0) (fits : view.frame.toNat + 280 < 2^64)
    (reservoirAway : MemoryWriter.BytesAway (view.frame + 240#64) (view.message + 48#64) 20)
    (normal : evaluateHOLFiniteState (bind {exceptionPost with locals := source.locals} "err" err) opcodeHandler = (none, post))
    (bounded : paid + (2 + FrameException.choicePrice err) ≤ ceiling) :
    FrameTerminal source post view.frame view.continuation ceiling := by
  obtain ⟨funded, small, clock, fields, budget, done⟩ := FrameException.handler_after_frame_prefix
    source exceptionPost source post view err paid installed effect aligned fits reservoirAway normal
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  have globals := congrArg PanSemStateFiniteExact.globals fields
  change post.memaddrs = source.memaddrs at domain
  change post.globals = source.globals at globals
  refine ⟨⟨paid + (2 + FrameException.choicePrice err), bounded, funded, clock, fields, budget,
    by rw [globals]; exact view.ev, by rw [globals]; exact view.curCont,
    .marked 1#64 (by rw [domain]; exact view.continuationMapped) done (by decide)⟩, ?_⟩
  let handler := bind {exceptionPost with locals := source.locals} "err" err
  have handlerEffect : FramePrefixEffect source handler view.frame paid := effect.of_emptyLocals rfl
  let current := view.after_frame_prefix handlerEffect aligned fits reservoirAway
  have installedCurrent : Input.OriginalCode.Installed handler.code := by rw [handlerEffect.code_eq]; exact installed
  have errLocal : handler.locals.lookup (ofString "err") = some (.val (.word err)) := bind_lookup_same _ _ _
  have monotone := FrameException.handler_used_monotone handler post current err installedCurrent errLocal normal
  have memoryEq := FrameException.handler_memory handler post current err installedCurrent errLocal normal
  refine ⟨?_, ?_⟩
  · change (wordAt handler.memory (view.frame + 184#64)).toNat ≤ (wordAt post.memory (view.frame + 184#64)).toNat at monotone
    simpa only [wordAt, handlerEffect.used] using monotone
  · intro address notSP footerAway notFrame notCont
    rw [memoryEq]
    exact (FrameException.memory_after_away handler.memory view.frame view.continuation err view.empty current.gas view.spill view.reservoir address notFrame notCont).trans
      (handlerEffect.outside address notSP footerAway)

theorem FrameTerminal.of_scopes {source phase endpoint post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont : BitVec 64} {ceiling : Nat} (terminal : FrameTerminal phase endpoint frame cont ceiling)
    (start : emptyLocalsHOLFinite phase = emptyLocalsHOLFinite source)
    (finish : emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint) : FrameTerminal source post frame cont ceiling := by
  have before := congrArg PanSemStateFiniteExact.memory start
  have after := congrArg PanSemStateFiniteExact.memory finish
  change phase.memory = source.memory at before
  change post.memory = endpoint.memory at after
  exact ⟨terminal.completion.of_scopes start finish, by rw [after, ← before]; exact terminal.memoryEffect⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.frame_terminal_after_prefix
#print axioms InitECandidate.Solver.GasBudget.RunFrames.FrameTerminal.of_scopes

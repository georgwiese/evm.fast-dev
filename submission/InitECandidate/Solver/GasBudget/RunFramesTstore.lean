import InitECandidate.Solver.GasBudget.DispatchTstorePrefix
import InitECandidate.Solver.GasBudget.RunFramesActiveCharge

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real caught TSTORE execution includes its actual static-mode guard,
underflow/charge checks and handler. It either terminates the current frame
within nine source clocks or reaches the genuine storage suffix after100gas. -/
theorem caught_tstore (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (sp used : BitVec 64) (read : eval source opcodeArgument = some (.val (.word 93#64)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    TerminalPrefix source post view.frame view.continuation 9 ∨
    ∃ ready, ChargeEvent source ready view.frame 6 100 ∧ ProgramSuffixFinish source post OpcodeTstore.suffix ready := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = 93#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, ready, inner, returned, event, suffixRun, scopeEq⟩ :=
      OpcodeDispatch.tstore_normal_prefix entry target view.frame binding installed view.ev view.cap _ bodyRun
    refine Or.inr ⟨ready, event.prepend before, Or.inl ⟨inner, returned, suffixRun, ?_⟩⟩
    rw [postEq]
    exact scopeEq
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    rcases OpcodeDispatch.tstore_exception_prefix entry target view.frame sp view.gas used binding installed shapes view.ev
        spMapped spCell (view.refillMapped 64 (by decide)) (view.haltMapped 184 (by decide)) view.gasCell usedCell view.cap
        (ofString "EvmErr") (.val (.word err)) bodyRun with failed | charged
    · obtain ⟨paid, bound, effect⟩ := failed
      have total := before.trans effect
      apply Or.inl
      apply terminal_after_prefix source target post view err (1 + paid) 9 installed total handlerRun
      have price : 2 + FrameException.choicePrice err ≤ 3 := by unfold FrameException.choicePrice; split <;> decide
      omega
    · obtain ⟨ready, inner, event, suffixRun, scopeEq⟩ := charged
      exact Or.inr ⟨ready, event.prepend before, Or.inr ⟨inner, target, err, suffixRun, scopeEq, handlerRun⟩⟩

theorem active_tstore (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (running pc length sp used : BitVec 64) (header : ActiveHeader source view.frame view.continuation running pc length)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 93#64)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    TerminalPrefix source post view.frame view.continuation 9 ∨
    ∃ ready, ChargeEvent source ready view.frame 6 100 ∧ ScopedProgramSuffixFinish source post OpcodeTstore.suffix ready := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let current := view.after_prefix setup
  rcases caught_tstore phase handled current sp used read installed shapes spMapped spCell usedCell caughtRun with terminal | charged
  · exact Or.inl (terminal.of_scopes rfl postScope)
  · obtain ⟨ready, event, finish⟩ := charged
    have total := event.prepend setup
    simp only [Nat.zero_add] at total
    exact Or.inr ⟨ready, total, phase, handled, rfl, postScope, finish⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_tstore
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_tstore

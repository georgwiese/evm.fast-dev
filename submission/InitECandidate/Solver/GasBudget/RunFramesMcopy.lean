import InitECandidate.Solver.GasBudget.DispatchMcopyPrefix
import InitECandidate.Solver.GasBudget.RunFramesActiveCharge

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual caught MCOPY: either a real pre-charge handler
marks the current frame done, or a positive dynamic copy/hash charge is reached
with its actual opcode/handler continuation trace retained. -/
theorem caught_mcopy (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (current sp used : BitVec 64) (read : eval source opcodeArgument = some (.val (.word 94#64)))
    (memory : MemoryExpansionCost.View source view.frame current)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    TerminalPrefix source post view.frame view.continuation (Mcopy.names.length + 54) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ Mcopy.names.length + 51 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready view.frame paid amount.toNat ∧
      Input.ExecutionTail ready Mcopy.suffix none post := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = 94#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, paid, amount, ready, bound, lower, event, tail⟩ :=
      OpcodeDispatch.mcopy_normal_prefix entry target view.frame current binding (memory.after_erase rfl) view.cap _ bodyRun
    have callerTail := Input.ExecutionTail.ignored_return tail source .one (by simp [shapeOfHOLExact, shapeEqHOL_eq_true])
    refine Or.inr ⟨1 + paid, amount, ready, by omega, lower, event.prepend before, ?_⟩
    apply Input.ExecutionTail.locals callerTail
    rw [postEq]
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    rcases OpcodeDispatch.mcopy_exception_prefix entry target view.frame current sp view.gas used binding (memory.after_erase rfl) shapes
        spMapped spCell (view.refillMapped 64 (by decide)) (view.haltMapped 184 (by decide)) view.gasCell usedCell view.cap
        (ofString "EvmErr") (.val (.word err)) bodyRun with failed | charged
    · obtain ⟨paid, bound, effect⟩ := failed
      have total := before.trans effect
      apply Or.inl
      apply terminal_after_prefix source target post view err (1 + paid) (Mcopy.names.length + 54) installed total handlerRun
      have price : 2 + FrameException.choicePrice err ≤ 3 := by unfold FrameException.choicePrice; split <;> decide
      omega
    · obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := charged
      exact Or.inr ⟨1 + paid, amount, ready, by omega, lower, event.prepend before,
        .handler tail source (ofString "err") opcodeHandler handlerRun⟩

theorem active_mcopy (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (current running pc length sp used : BitVec 64) (header : ActiveHeader source view.frame view.continuation running pc length)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 94#64)))
    (memory : MemoryExpansionCost.View source view.frame current)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    TerminalPrefix source post view.frame view.continuation (Mcopy.names.length + 54) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ Mcopy.names.length + 51 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready view.frame paid amount.toNat ∧
      Input.ExecutionTail ready Mcopy.suffix none post := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let phaseView := view.after_prefix setup
  rcases caught_mcopy phase handled phaseView current sp used read (memory.after_erase rfl) installed shapes spMapped spCell usedCell caughtRun with terminal | charged
  · exact Or.inl (terminal.of_scopes rfl postScope)
  · obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := charged
    have total := event.prepend setup
    simp only [Nat.zero_add] at total
    exact Or.inr ⟨paid, amount, ready, bound, lower, total, .locals tail postScope⟩

theorem mcopy_prefix_ceilings : Mcopy.names.length + 51 ≤ 54 ∧ Mcopy.names.length + 54 ≤ 57 := by
  decide

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_mcopy
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_mcopy
#print axioms InitECandidate.Solver.GasBudget.RunFrames.mcopy_prefix_ceilings

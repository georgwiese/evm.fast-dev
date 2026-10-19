import InitECandidate.Solver.GasBudget.RunFramesRevertOne
import InitECandidate.Solver.GasBudget.RunFramesChargeSite

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A completed real frame iteration with owned memory, a conserved regular
ledger, an actual done marker and an amortized paid-clock allowance. -/
def MemoryTerminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ paid, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
    MemoryExtend.View post frame base length capacity pointer scratch ∧
    regularBudget post.memory frame = regularBudget source.memory frame ∧
    (wordAt source.memory (frame + 184#64)).toNat ≤ (wordAt post.memory (frame + 184#64)).toNat ∧
    (MemoryGasCost.resultWord length).toNat ≤ (wordAt post.memory (frame + 184#64)).toNat ∧
    post.memory (cont + 32#64) = .word 1#64 ∧ post.memaddrs (cont + 32#64) ∧
    post.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) ∧
    paid + MemoryExtend.potential oldLength oldCapacity ≤ MemoryExtend.potential length capacity + ceiling ∧
    (∀ query, Arenas.Outside base scratch query →
      (∀ offset ∈ revertWriteOffsets, query ≠ frame + BitVec.ofNat 64 offset) →
      query ≠ cont + 32#64 → post.memory query = source.memory query)

theorem precharge_memory_terminal (source exceptionPost post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base length capacity pointer scratch err : BitVec 64) (paid : Nat)
    (memoryView : MemoryExtend.View source view.frame base length capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord length).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : StackPop.PrefixEffect source exceptionPost view.frame paid) (bound : paid ≤ 26)
    (continuationApart : ∀ offset ∈ ([24, 32, 40] : List Nat), view.frame + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (handlerRun : evaluateHOLFiniteState (bind {exceptionPost with locals := source.locals} "err" err) opcodeHandler = (none, post)) :
    MemoryTerminal source post view.frame view.continuation base scratch length capacity length capacity pointer 34 := by
  have terminal := terminal_after_prefix source exceptionPost post view err paid 29 installed effect handlerRun
    (by
      have price : 2 + FrameException.choicePrice err ≤ 3 := by
        unfold FrameException.choicePrice
        split <;> decide
      omega)
  obtain ⟨totalPaid, bounded, funded, clock, fields, budget, done, mapped, continuation, terminalMemory⟩ := terminal
  let handler := bind {exceptionPost with locals := source.locals} "err" err
  have handlerEffect : StackPop.PrefixEffect source handler view.frame paid := effect.of_emptyLocals rfl
  let current := view.after_prefix handlerEffect
  have buffer := memoryView.after_pops handlerEffect
  have postView := buffer.after_handler handler post current base length capacity pointer scratch err continuationApart (bind_lookup_same _ _ _) handlerRun
  refine ⟨totalPaid, funded, clock, postView, budget, terminalMemory.used, covered.trans terminalMemory.used, done, mapped, continuation, by omega, ?_⟩
  intro query outside apart notDone
  exact terminalMemory.outside query (apart 16 (by simp [revertWriteOffsets]))
    (by intro offset member; exact apart offset (List.mem_append_left _ member)) notDone

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.precharge_memory_terminal

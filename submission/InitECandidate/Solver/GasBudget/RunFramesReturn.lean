import InitECandidate.Solver.GasBudget.DispatchReturnErrors
import InitECandidate.Solver.GasBudget.RunFramesMemoryCompletion

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Complete real caught RETURN, deriving normal halt or either pre-charge
handler from the actual execution, including zero expansion charges. -/
theorem caught_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base current capacity pointer scratch sp : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (read : eval source opcodeArgument = some (.val (.word 243#64)))
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (runningMapped : source.memaddrs (view.frame + 104#64))
    (markedCell : source.memory (view.continuation + 32#64) = .word 0#64)
    (continuationOwned : Arenas.Outside base scratch (view.continuation + 32#64))
    (continuationApart : ∀ offset ∈ ([16, 24, 32, 40, 64, 184, 120, 128, 104] : List Nat),
      view.continuation + 32#64 ≠ view.frame + BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    ∃ length nextCapacity nextPointer,
      MemoryCompletion source post view.frame view.continuation base scratch current capacity length nextCapacity nextPointer 34 := by
  have installed := memoryView.installed
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = 243#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  have handlerApart : ∀ offset ∈ ([24, 32, 40] : List Nat), view.frame + BitVec.ofNat 64 offset ≠ view.continuation + 32#64 := by
    intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact Ne.symm (continuationApart _ (by simp))
  have shape := shapes Input.OriginalExceptions.Kind.EvmErr
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨start, size, paid, bound, funded, clock, postView, budget, credit, memoryCost, depth, running, globals, range, away⟩ :=
      OpcodeDispatch.return_body_normal entry target view.frame base current capacity pointer scratch (memoryView.after_erase rfl) view.cap covered binding _ bodyRun
    have fields := Input.evaluation_fields entry target OpcodeDispatch.body _ bodyRun
    have targetCap : regularBudget target.memory view.frame ≤ 16777216 := by rw [budget]; exact view.cap
    have targetUsedBound : (wordAt target.memory (view.frame + 184#64)).toNat ≤ 16777216 := by unfold regularBudget at targetCap; omega
    let amount := (MemoryExpansionCost.resultPair start size current).1
    let used := (wordAt source.memory (view.frame + 184#64)).toNat
    change (wordAt target.memory (view.frame + 184#64)).toNat = used + amount.toNat at credit
    have advance := MemoryExpansionCost.affordable start size current amount used (16777216 - used) memoryView.lengthAligned covered
      (by omega) (by omega) (Nat.le_refl _)
    have amortized := MemoryExtend.price_potential source view.frame base current capacity pointer scratch
      (MemoryExpansionCost.resultPair start size current).2 amount used memoryView advance
    have marker : target.memory (view.continuation + 32#64) = .word 0#64 :=
      (away _ continuationOwned (continuationApart 16 (by simp)) (continuationApart 32 (by simp)) (continuationApart 40 (by simp))
        (continuationApart 64 (by simp)) (continuationApart 184 (by simp)) (continuationApart 120 (by simp))
        (continuationApart 128 (by simp)) (continuationApart 104 (by simp))).trans markedCell
    subst post
    refine ⟨_, _, _, paid + 1, ?_, ?_, postView.after_erase rfl, budget, ?_, memoryCost, ?_, ?_, by omega, ?_⟩
    · change paid ≤ source.clock - 1 at funded
      omega
    · change target.clock = source.clock - 1 - paid at clock
      change target.clock = source.clock - (paid + 1)
      omega
    · change (wordAt source.memory (view.frame + 184#64)).toNat ≤ (wordAt target.memory (view.frame + 184#64)).toNat
      change (wordAt target.memory (view.frame + 184#64)).toNat = (wordAt source.memory (view.frame + 184#64)).toNat + amount.toNat at credit
      omega
    · exact .halted (by change target.memaddrs _; rw [fields.1]; exact view.continuationMapped) marker
        (by change target.memaddrs _; rw [fields.1]; exact runningMapped) running
    · exact (globals (ofString "cur_cont") (by decide)).trans view.curCont
    · intro query outside apart notCont
      exact away query outside (apart 16 (by simp [completionWriteOffsets, revertWriteOffsets]))
        (apart 32 (by simp [completionWriteOffsets, revertWriteOffsets])) (apart 40 (by simp [completionWriteOffsets, revertWriteOffsets]))
        (apart 64 (by simp [completionWriteOffsets, revertWriteOffsets, FrameException.writeOffsets]))
        (apart 184 (by simp [completionWriteOffsets, revertWriteOffsets, FrameException.writeOffsets]))
        (apart 120 (by simp [completionWriteOffsets, revertWriteOffsets, FrameException.writeOffsets]))
        (apart 128 (by simp [completionWriteOffsets, revertWriteOffsets, FrameException.writeOffsets]))
        (apart 104 (by simp [completionWriteOffsets]))
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    have errors := OpcodeDispatch.return_error_cases entry target installed binding (.val (.word err)) bodyRun
    rcases errors with stack | gas
    · have errEq : err = 2#64 := HolWordLab.word.inj (ValueHOL.val.inj stack)
      subst err
      obtain ⟨paid, bound, effect⟩ := OpcodeDispatch.return_stack_error_prefix entry target view.frame sp installed view.ev spMapped spCell shape binding bodyRun
      refine ⟨current, capacity, pointer, ?_⟩
      exact (precharge_memory_terminal source target post view base current capacity pointer scratch 2#64 (1 + paid) memoryView covered installed
        (before.trans effect) (by omega) handlerApart handlerRun).completion
    · have errEq : err = 4#64 := HolWordLab.word.inj (ValueHOL.val.inj gas)
      subst err
      obtain ⟨paid, bound, effect⟩ := OpcodeDispatch.return_gas_error_prefix entry target view.frame sp view.gas (wordAt source.memory (view.frame + 184#64))
        installed view.ev spMapped spCell (view.refillMapped 64 (by simp)) (view.haltMapped 184 (by simp)) view.gasCell (memory_word _ _) view.cap shape binding bodyRun
      refine ⟨current, capacity, pointer, ?_⟩
      exact (precharge_memory_terminal source target post view base current capacity pointer scratch 4#64 (1 + paid) memoryView covered installed
        (before.trans effect) (by omega) handlerApart handlerRun).completion

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_return

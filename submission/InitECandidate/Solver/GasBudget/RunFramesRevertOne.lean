import InitECandidate.Solver.GasBudget.DispatchRevert
import InitECandidate.Solver.GasBudget.FrameExceptionAccountedView
import InitECandidate.Solver.GasBudget.MemoryBufferHandlerView
import InitECandidate.Solver.GasBudget.MemoryExtendAmortized

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

def revertWriteOffsets : List Nat := FrameException.writeOffsets ++ [16, 32, 40]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem revert_one_handler (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base current capacity pointer scratch sp : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (reservoirOwned : Arenas.Outside base scratch (view.message + 48#64))
    (reservoirApart : ∀ offset ∈ ([16, 32, 40, 64, 184, 120, 128] : List Nat), view.message + 48#64 ≠ view.frame + BitVec.ofNat 64 offset)
    (continuationApart : ∀ offset ∈ ([24, 32, 40] : List Nat), view.frame + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (positive : 1 ≤ source.clock)
    (opLocal : callee.lookup (ofString "op") = some (.val (.word 253#64)))
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) OpcodeDispatch.body =
      (some (.exception (ofString "EvmErr") (.val (.word 1#64))), target))
    (handlerRun : evaluateHOLFiniteState (bind {target with locals := source.locals} "err" 1#64) opcodeHandler = (none, post)) :
    ∃ (start size : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 31 ∧
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      MemoryExtend.View post view.frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      regularBudget post.memory view.frame = regularBudget source.memory view.frame ∧
      (wordAt source.memory (view.frame + 184#64)).toNat ≤ (wordAt post.memory (view.frame + 184#64)).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (view.frame + 184#64)).toNat ∧
      post.memory (view.continuation + 32#64) = .word 1#64 ∧
      post.globals.lookup (ofString "cur_cont") = some (.val (.word view.continuation)) ∧
      paid + MemoryExtend.potential current capacity ≤
        MemoryExtend.potential (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
          (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) + 34 ∧
      (∀ query, Arenas.Outside base scratch query →
        (∀ offset ∈ revertWriteOffsets, query ≠ view.frame + BitVec.ofNat 64 offset) →
        query ≠ view.continuation + 32#64 → post.memory query = source.memory query) := by
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨start, size, prefixPaid, prefixBound, prefixFits, prefixClock, expandedView, prefixBudget, prefixCredit, memoryCost, depth, running, globals, range, prefixAway⟩ :=
    OpcodeDispatch.revert_body_exception1 entry target view.frame base current capacity pointer scratch sp (memoryView.after_erase rfl)
      view.cap covered spMapped spCell shape opLocal bodyRun
  change prefixPaid ≤ source.clock - 1 at prefixFits
  change target.clock = source.clock - 1 - prefixPaid at prefixClock
  have fields := Input.evaluation_fields entry target OpcodeDispatch.body _ bodyRun
  have headers (offset : Nat) (member : offset ∈ ([72, 112, 192] : List Nat)) :
      target.memory (view.frame + BitVec.ofNat 64 offset) = source.memory (view.frame + BitVec.ofNat 64 offset) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prefixAway (view.frame + 72#64) (memoryView.header_outside 72 (by decide)) (offsets_ne view.frame 72#64 16#64 (by decide)) (offsets_ne view.frame 72#64 32#64 (by decide)) (offsets_ne view.frame 72#64 40#64 (by decide)) (offsets_ne view.frame 72#64 64#64 (by decide)) (offsets_ne view.frame 72#64 184#64 (by decide)) (offsets_ne view.frame 72#64 120#64 (by decide)) (offsets_ne view.frame 72#64 128#64 (by decide))
    · exact prefixAway (view.frame + 112#64) (memoryView.header_outside 112 (by decide)) (offsets_ne view.frame 112#64 16#64 (by decide)) (offsets_ne view.frame 112#64 32#64 (by decide)) (offsets_ne view.frame 112#64 40#64 (by decide)) (offsets_ne view.frame 112#64 64#64 (by decide)) (offsets_ne view.frame 112#64 184#64 (by decide)) (offsets_ne view.frame 112#64 120#64 (by decide)) (offsets_ne view.frame 112#64 128#64 (by decide))
    · exact prefixAway (view.frame + 192#64) (memoryView.header_outside 192 (by decide)) (offsets_ne view.frame 192#64 16#64 (by decide)) (offsets_ne view.frame 192#64 32#64 (by decide)) (offsets_ne view.frame 192#64 40#64 (by decide)) (offsets_ne view.frame 192#64 64#64 (by decide)) (offsets_ne view.frame 192#64 184#64 (by decide)) (offsets_ne view.frame 192#64 120#64 (by decide)) (offsets_ne view.frame 192#64 128#64 (by decide))
  have reservoir : target.memory (view.message + 48#64) = source.memory (view.message + 48#64) :=
    prefixAway _ reservoirOwned (reservoirApart 16 (by simp)) (reservoirApart 32 (by simp)) (reservoirApart 40 (by simp))
      (reservoirApart 64 (by simp)) (reservoirApart 184 (by simp)) (reservoirApart 120 (by simp)) (reservoirApart 128 (by simp))
  let handler := bind {target with locals := source.locals} "err" 1#64
  let currentHandler : FrameException.View handler := view.after_accounted globals fields.1 prefixBudget headers reservoir
  have handlerOriginal : Input.OriginalCode.Installed handler.code := by
    change Input.OriginalCode.Installed target.code
    rw [fields.2.2.2]
    exact installed
  have errLocal : handler.locals.lookup (ofString "err") = some (.val (.word 1#64)) := bind_lookup_same _ _ _
  obtain ⟨handlerFits, handlerBound, handlerClock, canonical, handlerBudget, done⟩ :=
    FrameException.handler_normal handler post currentHandler 1#64 handlerOriginal errLocal handlerRun
  have handlerUsed := FrameException.handler_used_monotone handler post currentHandler 1#64 handlerOriginal errLocal handlerRun
  have handlerMemory := FrameException.handler_memory handler post currentHandler 1#64 handlerOriginal errLocal handlerRun
  have finalView := (expandedView.after_erase (show Input.LocalEffects.erase handler = Input.LocalEffects.erase target from rfl)).after_handler
    handler post currentHandler base _ _ _ scratch 1#64 continuationApart errLocal handlerRun
  change 2 ≤ target.clock at handlerFits
  change post.clock = target.clock - 2 at handlerClock
  change (wordAt target.memory (view.frame + 184#64)).toNat ≤ (wordAt post.memory (view.frame + 184#64)).toNat at handlerUsed
  have finalBudget : regularBudget post.memory view.frame = regularBudget source.memory view.frame := handlerBudget.trans prefixBudget
  let amount := (MemoryExpansionCost.resultPair start size current).1
  let used := (wordAt source.memory (view.frame + 184#64)).toNat
  change (wordAt target.memory (view.frame + 184#64)).toNat = used + amount.toNat at prefixCredit
  have targetCap : regularBudget target.memory view.frame ≤ 16777216 := by rw [prefixBudget]; exact view.cap
  have targetUsedBound : (wordAt target.memory (view.frame + 184#64)).toNat ≤ 16777216 := by unfold regularBudget at targetCap; omega
  have advance := MemoryExpansionCost.affordable start size current amount used (16777216 - used) memoryView.lengthAligned covered
    (by omega) (by omega) (Nat.le_refl _)
  have amortized := MemoryExtend.price_potential source view.frame base current capacity pointer scratch
    (MemoryExpansionCost.resultPair start size current).2 amount used memoryView advance
  refine ⟨start, size, prefixPaid + 3, by omega, ?_, ?_, finalView, finalBudget, ?_, memoryCost.trans handlerUsed, done, ?_, by omega, ?_⟩
  · rw [prefixClock] at handlerFits
    omega
  · rw [handlerClock, prefixClock]
    omega
  · dsimp only [used] at prefixCredit
    omega
  · rw [canonical]
    exact currentHandler.curCont
  · intro query outside apart notDone
    rw [handlerMemory]
    change FrameException.memoryAfter target.memory view.frame view.continuation 1#64 view.empty _ view.spill view.reservoir query = _
    rw [FrameException.memory_after_away _ _ _ _ _ _ _ _ _ (by intro offset member; exact apart offset (List.mem_append_left _ member)) notDone]
    exact prefixAway query outside (apart 16 (by simp [revertWriteOffsets])) (apart 32 (by simp [revertWriteOffsets]))
      (apart 40 (by simp [revertWriteOffsets])) (apart 64 (by simp [revertWriteOffsets, FrameException.writeOffsets]))
      (apart 184 (by simp [revertWriteOffsets, FrameException.writeOffsets])) (apart 120 (by simp [revertWriteOffsets, FrameException.writeOffsets]))
      (apart 128 (by simp [revertWriteOffsets, FrameException.writeOffsets]))

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.revert_one_handler

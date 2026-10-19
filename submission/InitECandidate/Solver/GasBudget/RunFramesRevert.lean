import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminal
import InitECandidate.Solver.GasBudget.DispatchRevertErrors
import InitECandidate.Solver.GasBudget.RevertNoReturn

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Every real normally completed caught REVERT iteration terminates its
current continuation. The complete error1, underflow2 and gas4 paths are
derived from the actual dispatcher and handler executions. -/
theorem caught_revert (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (base current capacity pointer scratch sp : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (view.frame + 184#64)).toNat)
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (read : eval source opcodeArgument = some (.val (.word 253#64)))
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (reservoirOwned : Arenas.Outside base scratch (view.message + 48#64))
    (reservoirApart : ∀ offset ∈ ([16, 32, 40, 64, 184, 120, 128] : List Nat), view.message + 48#64 ≠ view.frame + BitVec.ofNat 64 offset)
    (continuationApart : ∀ offset ∈ ([24, 32, 40] : List Nat), view.frame + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    ∃ length nextCapacity nextPointer,
      MemoryTerminal source post view.frame view.continuation base scratch current capacity length nextCapacity nextPointer 34 := by
  have installed := memoryView.installed
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = 253#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  have shape := shapes Input.OriginalExceptions.Kind.EvmErr
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, function, arguments, middle, selected, helperRun, scope⟩ := OpcodeDispatch.normal_helper entry target 253#64 binding _ bodyRun
    rw [OpcodeDispatch.selection_revert] at selected
    cases selected
    exact (RevertOpcode.call_not_normal entry middle installed helperRun).elim
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    have errors := OpcodeDispatch.revert_error_cases entry target installed binding (.val (.word err)) bodyRun
    rcases errors with revert | stack | gas
    · have errEq : err = 1#64 := HolWordLab.word.inj (ValueHOL.val.inj revert)
      subst err
      obtain ⟨start, size, paid, bound, funded, clock, postView, budget, used, memoryCost, done, continuation, potential, outside⟩ :=
        revert_one_handler source target post view base current capacity pointer scratch sp memoryView covered installed spMapped spCell shape
          reservoirOwned reservoirApart continuationApart callee positive binding bodyRun handlerRun
      have bodyFields := Input.evaluation_fields entry target OpcodeDispatch.body _ bodyRun
      let handler := bind {target with locals := source.locals} "err" 1#64
      have handlerFields := Input.evaluation_fields handler post opcodeHandler none handlerRun
      have mapped : post.memaddrs (view.continuation + 32#64) := by
        rw [handlerFields.1]
        change target.memaddrs _
        rw [bodyFields.1]
        exact view.continuationMapped
      exact ⟨_, _, _, paid, funded, clock, postView, budget, used, memoryCost, done, mapped, continuation, potential, outside⟩
    · have errEq : err = 2#64 := HolWordLab.word.inj (ValueHOL.val.inj stack)
      subst err
      obtain ⟨paid, bound, effect⟩ := OpcodeDispatch.revert_stack_error_prefix entry target view.frame sp installed view.ev spMapped spCell shape binding bodyRun
      refine ⟨current, capacity, pointer, ?_⟩
      exact precharge_memory_terminal source target post view base current capacity pointer scratch 2#64 (1 + paid) memoryView covered installed
        (before.trans effect) (by omega) continuationApart handlerRun
    · have errEq : err = 4#64 := HolWordLab.word.inj (ValueHOL.val.inj gas)
      subst err
      obtain ⟨paid, bound, effect⟩ := OpcodeDispatch.revert_gas_error_prefix entry target view.frame sp view.gas (wordAt source.memory (view.frame + 184#64))
        installed view.ev spMapped spCell (view.refillMapped 64 (by simp)) (view.haltMapped 184 (by simp)) view.gasCell (memory_word _ _) view.cap shape binding bodyRun
      refine ⟨current, capacity, pointer, ?_⟩
      exact precharge_memory_terminal source target post view base current capacity pointer scratch 4#64 (1 + paid) memoryView covered installed
        (before.trans effect) (by omega) continuationApart handlerRun

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_revert

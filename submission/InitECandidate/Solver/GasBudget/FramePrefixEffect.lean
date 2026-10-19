import InitECandidate.Solver.GasBudget.CallEntryTable
import InitECandidate.Solver.GasBudget.StackPopPrefixEffect

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact

/-- Actual pre-charge effects allowing CALL's original address footer in
addition to SP. Regular ledger words and nonlocal metadata are preserved. -/
structure FramePrefixEffect (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (paid : Nat) : Prop where
  fits : paid ≤ source.clock
  clock : target.clock = source.clock - paid
  fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock}
  budget : regularBudget target.memory frame = regularBudget source.memory frame
  used : target.memory (frame + 184#64) = source.memory (frame + 184#64)
  outside : ∀ query, query ≠ frame + 16#64 → MemoryWriter.BytesAway (frame + 240#64) query 20 → target.memory query = source.memory query

theorem StackPop.PrefixEffect.frame_effect {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : StackPop.PrefixEffect source target frame paid) : FramePrefixEffect source target frame paid :=
  ⟨effect.fits, effect.clock, effect.fields, effect.budget, effect.used, by intro query notSP away; exact effect.outside query notSP⟩

theorem FramePrefixEffect.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {first second : Nat}
    (before : FramePrefixEffect source middle frame first) (after : FramePrefixEffect middle target frame second) :
    FramePrefixEffect source target frame (first + second) := by
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := target.memory, clock := target.clock}) before.fields
  refine ⟨?_, by rw [after.clock, before.clock]; omega, after.fields.trans lift, after.budget.trans before.budget, after.used.trans before.used, ?_⟩
  · have firstFits := before.fits
    have secondFits := after.fits
    rw [before.clock] at secondFits
    omega
  · intro query notSP away
    exact (after.outside query notSP away).trans (before.outside query notSP away)

theorem FramePrefixEffect.masked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : Memory) (frame : BitVec 64) (name : String) (paid : Nat)
    (funded : paid ≤ source.clock) (aligned : frame.toNat % 8 = 0) (fits : frame.toNat + 280 < 2^64)
    (outside : ∀ query, MemoryWriter.BytesAway (frame + 240#64) query 20 → memory query = source.memory query) :
    FramePrefixEffect source (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} name (frame + 240#64)) frame paid := by
  obtain ⟨budget, used⟩ := AddressMasked.budget_preserved source.memory memory frame aligned fits outside
  exact ⟨funded, rfl, rfl, budget, used, by intro query notSP away; exact outside query away⟩

theorem FramePrefixEffect.of_emptyLocals {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source middle frame paid) (same : emptyLocalsHOLFinite target = emptyLocalsHOLFinite middle) :
    FramePrefixEffect source target frame paid := by
  have memory := congrArg PanSemStateFiniteExact.memory same
  have clock := congrArg PanSemStateFiniteExact.clock same
  change target.memory = middle.memory at memory
  change target.clock = middle.clock at clock
  refine ⟨effect.fits, clock.trans effect.clock, ?_, ?_, ?_, ?_⟩
  · rw [same, effect.fields, memory, clock]
  · rw [memory]; exact effect.budget
  · rw [memory]; exact effect.used
  · intro query notSP away
    rw [memory]
    exact effect.outside query notSP away

theorem FramePrefixEffect.restore {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    FramePrefixEffect source (WitnessRadix.QueryBranch.restore saved name target) frame paid :=
  effect.of_emptyLocals rfl

theorem FramePrefixEffect.code_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) : target.code = source.code := by
  have same := congrArg PanSemStateFiniteExact.code effect.fields
  exact same
theorem FramePrefixEffect.globals_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) : target.globals = source.globals := by
  have same := congrArg PanSemStateFiniteExact.globals effect.fields
  exact same
theorem FramePrefixEffect.memaddrs_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) : target.memaddrs = source.memaddrs := by
  have same := congrArg PanSemStateFiniteExact.memaddrs effect.fields
  exact same
theorem FramePrefixEffect.eshapes_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) : target.eshapes = source.eshapes := by
  have same := congrArg PanSemStateFiniteExact.eshapes effect.fields
  exact same

theorem FramePrefixEffect.buffer_view {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64} {paid : Nat}
    (effect : FramePrefixEffect source target frame paid) (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) : MemoryExtend.View target frame base length capacity pointer scratch := by
  have header (offset : Nat) (small : offset < 240) (notSP : BitVec.ofNat 64 offset ≠ 16#64) :
      target.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) :=
    effect.outside _ (offsets_ne frame _ _ notSP) (AddressMasked.header_away frame offset aligned view.frameFits small)
  have current := view.with_memory target.memory
    ((header 24 (by decide) (by decide)).trans view.baseCell)
    ((header 32 (by decide) (by decide)).trans view.lengthCell)
    ((header 40 (by decide) (by decide)).trans view.capacityCell)
  have erased := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) effect.fields
  exact current.after_erase erased

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.frame_effect
#print axioms InitECandidate.Solver.GasBudget.FramePrefixEffect.trans
#print axioms InitECandidate.Solver.GasBudget.FramePrefixEffect.masked
#print axioms InitECandidate.Solver.GasBudget.FramePrefixEffect.of_emptyLocals
#print axioms InitECandidate.Solver.GasBudget.FramePrefixEffect.buffer_view

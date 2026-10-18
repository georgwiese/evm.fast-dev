import InitECandidate.Solver.GasBudget.OpcodeChargeException

namespace InitECandidate.Solver.GasBudget.OpcodeChargePrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Real caller or sp-only prefixes retain the charge event and exact
physical effects, with their actually paid source clocks added. -/
theorem ChargedEffect.prepend {source middle ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame sp remaining amount : BitVec 64} {popCount overhead paid : Nat}
    (prior : StackPop.PrefixEffect source middle frame paid)
    (effect : ChargedEffect middle ready frame sp remaining popCount amount overhead) :
    ChargedEffect source ready frame sp remaining popCount amount (overhead + paid) := by
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) prior.fields
  refine ⟨?_, ?_, effect.fields.trans lift, effect.budget.trans prior.budget, ?_, effect.spCell, effect.depth, ?_⟩
  · have first := prior.fits
    have next := effect.fits
    rw [prior.clock] at next
    omega
  · rw [effect.clock, prior.clock]
    omega
  · rw [effect.used]
    simp only [wordAt, prior.used]
  · intro address notSP notGas notUsed
    exact (effect.outside address notSP notGas notUsed).trans (prior.outside address notSP)

end InitECandidate.Solver.GasBudget.OpcodeChargePrefix

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargePrefix.ChargedEffect.prepend

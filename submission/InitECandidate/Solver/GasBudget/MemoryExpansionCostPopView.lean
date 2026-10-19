import InitECandidate.Solver.GasBudget.MemoryExpansionCostProgram
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem View.after_pops {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame current : BitVec 64} {paid : Nat}
    (view : View source frame current) (effect : StackPop.PrefixEffect source target frame paid) : View target frame current := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [effect.code_eq]; exact view.installed
  · rw [effect.globals_eq]; exact view.ev
  · rw [effect.memaddrs_eq]; exact view.mapped
  · exact (effect.outside _ (offsets_ne frame 32#64 16#64 (by decide))).trans view.cell

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.View.after_pops

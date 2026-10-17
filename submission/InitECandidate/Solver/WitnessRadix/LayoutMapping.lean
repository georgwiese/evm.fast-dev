import InitECandidate.Solver.WitnessRadix.BackingLayout

/-! Readable allocated cells, independent of the replacement scatter program. -/
namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def Mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) : Prop :=
  ∀ pool offset, offset % 8 = 0 → offset + 8 ≤ size layout pool → source.memaddrs (cell layout pool offset)


end InitECandidate.Solver.WitnessRadix.BackingLayout

import InitECandidate.Solver.Mpt.AccountNewProgram
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Mpt.AccountNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem tail_quiet (code) : Input.QuietClock.Preserves code tail := by
  simp only [tail,afterNonce,afterBalance,afterRoot,rootStore,hashStore]
  repeat first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.returned code _

/-- Two source call/loop ticks cover every constructor outcome, including
an allocator guard failure. Normal construction spends exactly one. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 2 := by
  rw [body_shape]
  exact WitnessRadix.PersistentAlloc.scoped_price code installed (ofString "a") .one [.const 56#64] tail 0
    (Input.ClockCost.of_quiet code tail (tail_quiet code))

end InitECandidate.Solver.Mpt.AccountNew

#print axioms InitECandidate.Solver.Mpt.AccountNew.tail_quiet
#print axioms InitECandidate.Solver.Mpt.AccountNew.body_price

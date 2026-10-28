import InitECandidate.Solver.Input.CurrentHash.PContainerProgram
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.GlobalEffectsLoop

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem bit_step_other (key : MlS) (different : key ≠ ofString "i") : LocalPrefix key bitStep := by
  rw [body_shape.2.2.2.2.2.2.2.2.1]
  exact .seq (.storeByte _ _) (.assign _ _ different)

theorem bit_step_quiet (code) : QuietClock.Preserves code bitStep := by
  rw [body_shape.2.2.2.2.2.2.2.2.1]
  exact QuietClock.sequence code _ _ (StraightBody.byte_clock code _ _) (QuietClock.assign code _ _)

theorem bit_step_advances : CounterFlow.Advances (ofString "i") 1 bitStep := by
  rw [body_shape.2.2.2.2.2.2.2.2.1]
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.storeByte _ _)) (CounterFlow.increment _)

/-- Actual signed activity counter: one source loop tick per field, including
failed byte reads/stores. The nonnegative word range is checked explicitly. -/
theorem bit_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n index : Nat)
    (small : n < 2^63) (inside : index ≤ n)
    (position : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock - (evaluateHOLFiniteState source bitLoop).2.clock ≤ n-index := by
  have number : (BitVec.ofNat 64 index).toNat = index := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have paid := CounterFlow.signed_loop_cost source.code (ofString "i") (ofString "n") bitStep 0 n small
    (ClockCost.of_quiet source.code bitStep (bit_step_quiet source.code)) bit_step_advances (bit_step_other _ (by decide))
    source (BitVec.ofNat 64 index) rfl position count (by rw [number]; exact inside)
  rw [body_shape.2.2.2.2.2.2.2.1]
  simpa only [Nat.zero_add, Nat.one_mul, number, test, localVar] using paid

theorem bit_loop_globals (key : MlS) (code) : GlobalEffects.Preserves key code bitLoop := by
  rw [body_shape.2.2.2.2.2.2.2.1,body_shape.2.2.2.2.2.2.2.2.1]
  exact GlobalEffects.loop key code _ _ (GlobalEffects.sequence key code _ _ (GlobalEffects.byte_store key code _ _) (GlobalEffects.assign key code _ _))

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_step_other
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_step_quiet
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_step_advances
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_loop_globals

import InitECandidate.Solver.WitnessRadix.CopyGeneralCall
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString CopyContext

/-- Actual normal original memcpy derives its own clock allowance and exact
full caller state. Source/destination mapping is physical entry ownership. -/
theorem call_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values dst src length))
    (code : source.code.lookup (ofString "memcpy") = some (formals, Copy32.body, .one))
    (mapped : Mapped source src dst length) (small : length + 32 < 2 ^ 64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memcpy") arguments) = (none, target)) :
    cost src dst length + 1 ≤ source.clock ∧ cost src dst length + 1 ≤ length + 1 ∧ target = callState source src dst length := by
  classical
  let extra := cost src dst length + 1
  let padded := {source with clock := source.clock + extra}
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) arguments = some (values dst src length) := by
    change evalListHOLExact (stateAddClock source.toExact extra) arguments = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  have paddedMapped : Mapped padded src dst length := Mapped.of_domain source padded src dst length rfl mapped
  have actual := call_execute padded arguments src dst length paddedArgs code paddedMapped small (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none, none)) (ofString "memcpy") arguments) source none target extra
    ⟨normal, by intro impossible; cases impossible⟩
  have same := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + extra} = callState padded src dst length at same
  have stripped := InitECandidate.Solver.strip_full_clock_padding source target
    {source with memory := resultMemory source.memory source.be src dst length} extra extra (by omega) same
  exact ⟨stripped.1, by have bound := cost_le src dst length; omega, stripped.2⟩

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_normal

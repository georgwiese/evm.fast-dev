import InitECandidate.Solver.WitnessRadix.ZeroCall
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual successful aligned memzero, with exact clock funding derived
from execution. In particular its heap cursor and caller locals survive. -/
theorem call_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values dst length))
    (code : source.code.lookup (ofString "memzero") = some (formals, body, .one))
    (small : length + 32 < 2 ^ 64) (multiple : length % 8 = 0) (aligned : dst.toNat % 8 = 0)
    (mapped : ∀ offset, offset + 8 ≤ length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") arguments) = (none, target)) :
    price length + 1 ≤ source.clock ∧
      target = {source with memory := finalMemory source.memory dst length, clock := source.clock - (price length + 1)} := by
  classical
  let extra := price length + 1
  let padded := {source with clock := source.clock + extra}
  have lifted := panPropsEvaluateAddClockEq (.call (some (none, none)) (ofString "memzero") arguments) source none target extra
    ⟨normal, by intro impossible; cases impossible⟩
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) arguments = some (values dst length) := by
    change evalListHOLExact (stateAddClock source.toExact extra) arguments = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  have actual := call_execute padded arguments dst length paddedArgs code small multiple aligned mapped (by change extra ≤ source.clock + extra; omega)
  have same := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + extra} = {source with memory := finalMemory source.memory dst length, clock := source.clock + extra - extra} at same
  have clock := congrArg PanSemStateFiniteExact.clock same
  change target.clock + extra = source.clock + extra - extra at clock
  have fits : extra ≤ source.clock := by omega
  have spent : target.clock = source.clock - extra := by omega
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with clock := target.clock}) same
  change target = {source with memory := finalMemory source.memory dst length, clock := target.clock} at reset
  rw [spent] at reset
  exact ⟨fits, reset⟩

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.call_normal

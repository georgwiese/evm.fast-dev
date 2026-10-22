import InitECandidate.Solver.Input.ConstantStrideLoopCost
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.ClockCostAssignedBody
import InitECandidate.Solver.Input.QuietClockEffects
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch Input Input.CounterFlow

/-- The actual FFI clause spends no source call/loop clock, even if its
argument reads or the oracle stop. Its target/oracle work is separate. -/
theorem permutation_body_cost (code) : ClockCost.Bound code Keccak.f1600Body 0 := by
  rw [Keccak.body_shape]
  exact ClockCost.of_quiet code _ (QuietClock.sequence code _ _
    (QuietClock.external code _ _ _ _ _) (QuietClock.returned code _))

theorem lane_advance (unaligned : Bool) : Advances (ofString "i") 8 (laneBody unaligned) := by
  change Advances (ofString "i") (0+8) (.seq _ _)
  apply CounterFlow.sequence
  · exact CounterFlow.preserved (ofString "i") _ (LocalPrefix.store _ _)
  · exact CounterFlow.increment_by (ofString "i") 8

theorem lane_safe (unaligned : Bool) : LocalPrefix (ofString "stp") (laneBody unaligned) :=
  .seq (.store _ _) (.assign _ _ (by decide))

theorem loop_cost (code) (unaligned : Bool) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : source.code=code) (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64))) :
    source.clock-(evaluateHOLFiniteState source (loop unaligned)).2.clock≤17 := by
  have quiet : QuietClock.Preserves code (laneBody unaligned):=
    QuietClock.sequence code _ _ (QuietClock.store code _ _) (QuietClock.assign code _ _)
  have priced:=CounterFlow.constant_stride_cost code (ofString "i") (ofString "stp") (laneBody unaligned) 0 8 136
    (by decide) (by decide) (by decide) (ClockCost.of_quiet code _ quiet) (lane_advance unaligned) (lane_safe unaligned)
    source 0#64 installed counter (by decide) (dvd_zero 8)
  simpa only [loop,condition,localVar,Nat.zero_add,Nat.one_mul,BitVec.toNat_ofNat,Nat.zero_mod,Nat.sub_zero] using priced

/-- Every outcome of unchanged absorb_block uses at most seventeen lane
ticks and one permutation call. No pointer, mapping or oracle premise. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body 18 := by
  have callPrice:=ClockCost.assigned_body code none (ofString "keccak_f1600") [localVar "stp"] _ Keccak.f1600Body .one 0
    (Keccak256.permutation_original_code code installed) (permutation_body_cost code)
  have tailPrice : ClockCost.Bound code tail 1:=by
    simpa only [tail,Nat.add_zero] using ClockCost.sequence code _ _ 1 0 callPrice (ClockCost.returned code (.const 0#64))
  intro source codeEq
  rw [body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 18 rfl
  let entered:=QueryBranch.bind source "i" 0#64
  have branches:=ClockCost.conditional_current entered alignment (loop false) (loop true) 17 17
    (loop_cost code false entered codeEq (bind_lookup_same _ _ _))
    (loop_cost code true entered codeEq (bind_lookup_same _ _ _))
  exact ClockCost.sequence_current entered _ tail 17 1 branches (by intro current currentCode; exact tailPrice current (currentCode.trans codeEq))

theorem call_cost (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "keccak_absorb_block") arguments) 19 :=
  ClockCost.assigned_body code none (ofString "keccak_absorb_block") arguments _ body .one 18
    (Keccak256.block_original_code code installed) (body_cost code installed)

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.permutation_body_cost
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.lane_advance
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.loop_cost
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.body_cost
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.call_cost

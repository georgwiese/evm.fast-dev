import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Program
import InitECandidate.Solver.Input.ClockCostCurrentValue
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- The real signed inner counter starts at zero, remains nonnegative and
can run at most eight bit tests, including early returns and short clocks. -/
theorem different_cost (code) : ClockCost.Bound code different 8 := by
  intro source installed
  rw [shapes.2.2.2.2.2.2.1]
  apply ClockCost.declared_value_current source _ _ _ (.val (.word 0#64)) bitLoop 8
  · simp [eval,evalHOLExact]
  · let entry := setVarHOLFinite (ofString "j") (.val (.word 0#64)) source
    change entry.clock - (evaluateHOLFiniteState entry bitLoop).2.clock ≤ 8
    rw [shapes.2.2.2.2.2.2.2.1]
    have cost := CounterFlow.loop_snapshot_cost code (ofString "j") (ofString "x")
      (entry.locals.lookup (ofString "x")) bitLimit bitStep 0 8 (by decide)
      (by
        intro current word currentCell saved bounded
        have small : word.toNat < 9223372036854775808 := by omega
        simp [bitLimit,localVar,evalHOLFinite,evalHOLExact,currentCell,wordCmpHOL,
          holAsmSignedLess,small])
      (ClockCost.of_quiet code bitStep (bit_quiet code)) bit_advance (bit_flow _ (by decide))
      entry 0#64 installed
      (by simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]) rfl (by decide)
    simpa using cost

theorem step_cost (code) : ClockCost.Bound code step 8 := by
  rw [shapes.2.2.2.1,shapes.2.2.2.2.1,shapes.2.2.2.2.2.1]
  apply ClockCost.declared code _ _ _ _ 8
  have choicePrice := ClockCost.conditional code (.cmp .notEqual (localVar "x") (.const 0#64))
    different .skip 8 0 (different_cost code) (ClockCost.skip code)
  have price := ClockCost.sequence code _ (increment "i") 8 0 (by simpa using choicePrice)
    (ClockCost.assign code _ _)
  simpa using price

/-- No mapped byte contents or successful future reads are assumed. Every
actual outcome of the unchanged scan is charged, at any entering clock. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (word : BitVec 64) (small : length < 2^64)
    (counterCell : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 9 * (length - word.toNat) := by
  rw [shapes.2.2.1]
  exact CounterFlow.loop_snapshot_cost source.code (ofString "i") (ofString "key_len")
    (some (.val (.word (BitVec.ofNat 64 length)))) test step 8 length small
    (by
      intro current number currentCell saved bounded
      have lengthMod : length % 18446744073709551616 = length := Nat.mod_eq_of_lt small
      simp [test,localVar,evalHOLFinite,evalHOLExact,currentCell,saved,wordCmpHOL,
        BitVec.lt_def,BitVec.toNat_ofNat,lengthMod])
    (step_cost source.code) step_advance (step_flow _ (by decide) (by decide) (by decide))
    source word rfl counterCell lengthCell initial

/-- Actual htab_first_diff body allowance. In the current database callers,
length32 gives288source ticks; straight-line target work remains separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (small : length < 2^64)
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 9 * length := by
  rw [shapes.1]
  apply ClockCost.declared_value_current source _ _ _ (.val (.word 0#64)) afterI _
  · simp [eval,evalHOLExact]
  · let entry := setVarHOLFinite (ofString "i") (.val (.word 0#64)) source
    change entry.clock - (evaluateHOLFiniteState entry afterI).2.clock ≤ 9 * length
    have currentCell : entry.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have saved : entry.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))) := by
      simpa [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "i" ≠ ofString "key_len" from by decide] using lengthCell
    have price := loop_cost entry length 0#64 small currentCell saved (by simp)
    rw [shapes.2.1]
    have result := ClockCost.sequence_reached_current entry loop (.return (.panop .mul [localVar "key_len",.const 8#64])) (9 * length) 0
      (by simpa using price) (by intro middle run; exact ClockCost.returned middle.code _ middle rfl)
    simpa using result

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.different_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.body_cost

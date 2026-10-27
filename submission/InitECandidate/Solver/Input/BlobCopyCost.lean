import InitECandidate.Solver.Input.BlobProgram
import InitECandidate.Solver.Input.SharedLoadLocal
import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.QuietClockShared

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem copy_body_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    LocalSummary (ofString "len") copyBody source := by
  apply local_summary_sequence
  · exact shared_load_local _ _ _ _ (by decide)
  · exact (LocalPrefix.seq (.store _ _) (.assign _ _ (by decide))).summary_full

theorem copy_advance : CounterFlow.Advances (ofString "i") 8 copyBody := by
  exact CounterFlow.sequence _ _ _ 0 8
    (CounterFlow.shared_load _ _ _ _ (by decide))
    (CounterFlow.sequence _ _ _ 0 8 (CounterFlow.preserved _ _ (.store _ _))
      (CounterFlow.increment_by _ 8))

theorem copy_body_cost (code) : ClockCost.Bound code copyBody 0 :=
  ClockCost.sequence code _ _ 0 0 (ClockCost.shared_load code _ _ _ _)
    (ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.assign code _ _))

/-- Every outcome of the unchanged current input-copy loop, including failed
reads and stores. No readable host arena or successful future copy is assumed. -/
theorem copy_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (word : BitVec 64) (small : length ≤ 1073741808)
    (counter : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (limit : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length + 7) :
    source.clock - (evaluateHOLFiniteState source copyLoop).2.clock ≤
      (length + 7 - word.toNat) / 8 := by
  have cost := CounterFlow.unsigned_stride_cost source.code (ofString "i") (ofString "len")
    copyBody 0 8 length (by omega) (by omega) (copy_body_cost source.code) copy_advance
    copy_body_local source word rfl counter limit (by omega)
  have arithmetic : length + 8 - 1 = length + 7 := by omega
  simpa only [copyLoop, copyCondition, localVar, Nat.zero_add, Nat.one_mul, arithmetic] using cost

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_body_local
#print axioms InitECandidate.Solver.Input.Blob.copy_advance
#print axioms InitECandidate.Solver.Input.Blob.copy_body_cost
#print axioms InitECandidate.Solver.Input.Blob.copy_loop_cost

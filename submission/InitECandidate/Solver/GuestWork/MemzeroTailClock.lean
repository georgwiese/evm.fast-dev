import InitECandidate.Solver.GuestWork.MemzeroTailRank
import InitECandidate.Solver.FlattenWeighted.LoopTimeout

namespace InitECandidate.Solver.GuestWork.MemzeroTail
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps
open InitECandidate.Solver.FlattenWeighted

/-- A concrete sufficient initial clock for the fixed byte loop. -/
def clockBudget (length index : BitVec 64) : Nat :=
  (length.toNat - index.toNat + 1) * 3 + 1

theorem enough_clock {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index)) :
    (evaluate (.loop body, {source with clock := clockBudget length index})).1 ≠ some .timeOut := by
  apply basicLoop_noTimeout body body_basic
    {source with clock := clockBudget length index} ((length.toNat - index.toNat + 1) * 3)
  · exact loop_clock _ base length index hbase hlength hindex
  · simp [clockBudget]

/-- The bounded execution also has the source-only work derivation needed by
flattening; no target execution is assumed. -/
theorem bounded_paid {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index)) :
    PaidProp ((length.toNat - index.toNat + 1) * 29) (.loop body)
      {source with clock := clockBudget length index} :=
  workPaid (loop_work _ base length index hbase hlength hindex)

end InitECandidate.Solver.GuestWork.MemzeroTail
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.enough_clock
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.bounded_paid

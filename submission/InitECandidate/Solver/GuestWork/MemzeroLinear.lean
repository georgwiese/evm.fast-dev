import InitECandidate.Solver.GuestWork.MemzeroEntry

namespace InitECandidate.Solver.GuestWork.MemzeroEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

theorem workBudget_linear (length : BitVec 64) : workBudget length ≤ 17 * length.toNat + 447 := by
  dsimp only [workBudget, MemzeroAligned.quadCount, MemzeroAligned.wordCount]
  omega

theorem consumedBudget_linear (length : BitVec 64) : consumedBudget length ≤ length.toNat + 43 := by
  dsimp only [consumedBudget, MemzeroAligned.quadCount, MemzeroAligned.wordCount]
  omega

/-- A uniform per-call bound for later guest accounting. The caller must prove
that its actual length fits the supplied maximum and that guard addition cannot
wrap. The bounded execution has the complete original result and final state
apart from unused clock; its Work budget translates through workPaid. -/
theorem bounded_execution_linear {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (execution : evaluate (Named78.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named78.2, {source with clock := maximumBytes + 44}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named78.2 {source with clock := maximumBytes + 44} (17 * maximumBytes + 447) := by
  have workLe := workBudget_linear length
  have clockLe := consumedBudget_linear length
  have block : BlockBound (C := C) (F := F) Named78.2 (pre base length) (fun _ => True)
      (17 * maximumBytes + 447) (maximumBytes + 43) :=
    (entryBound base length (by omega)).weaken (fun _ h => h) (fun _ h => h) (by omega) (by omega)
  exact block.boundedExecution (fun _ _ h => h) source post result ⟨hbase, hlength⟩ execution notTimeout

end InitECandidate.Solver.GuestWork.MemzeroEntry
#print axioms InitECandidate.Solver.GuestWork.MemzeroEntry.workBudget_linear
#print axioms InitECandidate.Solver.GuestWork.MemzeroEntry.consumedBudget_linear
#print axioms InitECandidate.Solver.GuestWork.MemzeroEntry.bounded_execution_linear

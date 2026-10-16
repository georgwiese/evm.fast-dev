import InitECandidate.Solver.FlattenWeighted.LocalFrame
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroFrame
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Actual memzero preserves its caller's return register, length, stack,
metadata and heap-base registers on every non-timeout exit, including errors. -/
theorem protected_register {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (reg : Nat) (protectedReg : reg ∈ [1, 11, 24, 25, 26])
    (execution : evaluate (Named78.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    post.regs.lookup reg = source.regs.lookup reg ∧ post.code = source.code := by
  have checked : keepsLocal reg Named78.2 = true := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at protectedReg
    rcases protectedReg with rfl | rfl | rfl | rfl | rfl <;> decide
  exact localFrame Named78.2 reg checked source post result execution notTimeout

/-- The same register preservation at the actual returning-call entry state. -/
theorem entered_register {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (label offset reg : Nat) (protectedReg : reg ∈ [11, 24, 25, 26])
    (execution : evaluate (Named78.2,
      StackSemStateOps.decClock (StackSemStateOps.setVar 1 (.loc label offset) source)) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    post.regs.lookup reg = source.regs.lookup reg ∧ post.code = source.code := by
  have member : reg ∈ [1, 11, 24, 25, 26] := List.mem_cons.mpr (Or.inr protectedReg)
  have notLink : reg ≠ 1 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at protectedReg
    rcases protectedReg with rfl | rfl | rfl | rfl <;> decide
  simpa [StackSemStateOps.decClock, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, notLink] using
    protected_register _ post result reg member execution notTimeout

end InitECandidate.Solver.GuestWork.MemzeroFrame
#print axioms InitECandidate.Solver.GuestWork.MemzeroFrame.protected_register
#print axioms InitECandidate.Solver.GuestWork.MemzeroFrame.entered_register

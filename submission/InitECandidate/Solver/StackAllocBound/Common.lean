import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Defs

/-! Zero-extra-clock strengthening for heap-allocation lowering's non-allocating
program class. The original register, stack, buffer and compiler premises and
postconditions are retained. This module states the invariant only. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect

def ZeroGoal {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width)),
    StackSemEvaluate.evaluate (p, s) = (r, t) → r ≠ some .error →
    StackProps.allocArg p → Pre cr c s regs →
    ∃ ck regs1, ck = 0 ∧
      StackSemEvaluate.evaluate ((comp n m p).1, Tgt anything cr c s ck regs) =
        (r, Res anything cr c t regs1) ∧ Post r t regs1

end InitECandidate.Solver.StackAllocBound

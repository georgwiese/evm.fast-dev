import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate
import InitECandidate.Solver.ClockBounds

/-! Clock bounds for the actual challenge evaluator, without baseline proof
imports. A terminal dispatch consumes one clock unit. A known prefix shift
transports a numerical bound; the prefix cost remains an explicit obligation. -/
namespace InitECandidate.Solver.TargetClock
open Flapjack

theorem zero_not_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms post : S)
    (outcome : HolOutcome) (finalFfi : HolFfiState σ) :
    evaluateTargetHOL mc ffi 0 ms ≠ (.halt outcome, post, finalFfi) := by
  simp [evaluateTargetHOL]

theorem halt_dispatch_one {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (notOrdinary : ¬ (mc.progAddresses (mc.target.getPc ms) ∧
      mc.target.getPc ms ∉ mc.ffiEntryPcs))
    (atHalt : mc.target.getPc ms = mc.haltPc) :
    evaluateTargetHOL mc ffi 1 ms =
      (.halt (if mc.target.getReg ms mc.ptrReg = 0 then .success else .resourceLimitHit),
        ms, ffi) := by
  simp only [evaluateTargetHOL, if_neg notOrdinary, if_pos atHalt]

theorem bounded_prefix_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (before after post : S) (outcome : HolOutcome) (finalFfi : HolFfiState σ)
    (prefixCost budget : Nat)
    (shift : ∀ clock, evaluateTargetHOL mc ffi (prefixCost + clock) before =
      evaluateTargetHOL mc ffi clock after)
    (run : ∃ clock, clock ≤ budget ∧
      evaluateTargetHOL mc ffi clock after = (.halt outcome, post, finalFfi)) :
    ∃ clock, clock ≤ prefixCost + budget ∧
      evaluateTargetHOL mc ffi clock before = (.halt outcome, post, finalFfi) :=
  ClockBounds.prefix_within _ _ _ prefixCost budget shift run

end InitECandidate.Solver.TargetClock

#print axioms InitECandidate.Solver.TargetClock.zero_not_halt
#print axioms InitECandidate.Solver.TargetClock.halt_dispatch_one
#print axioms InitECandidate.Solver.TargetClock.bounded_prefix_halt

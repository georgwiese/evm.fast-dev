import InitECandidate.Solver.GuestWork.MemzeroTail

namespace InitECandidate.Solver.GuestWork.MemzeroTail
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps
open InitECandidate.Solver.FlattenWeighted

/-- Only the three registers used by the actual tail loop are constrained. -/
def invariant {C F : Type} (base length : BitVec 64)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  ∃ index : BitVec 64,
    state.regs.lookup 10 = some (.word base) ∧
    state.regs.lookup 11 = some (.word length) ∧
    state.regs.lookup 12 = some (.word index)

/-- Saturated remaining byte count; an index past the end immediately exits. -/
def remaining {C F : Type} (length : BitVec 64)
    (state : StackSemStateFiniteExact 64 C F) : Nat :=
  match state.regs.lookup 12 with
  | some (.word index) => length.toNat - index.toNat
  | _ => 0

theorem body_decreases {C F : Type} (base length : BitVec 64)
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (valid : invariant base length source)
    (execution : evaluate (body, source) = (result, post))
    (continues : StackSemControl.contLoop result = true) :
    invariant base length (decClock post) ∧
      remaining length (decClock post) < remaining length source := by
  obtain ⟨index, hbase, hlength, hindex⟩ := valid
  obtain ⟨nextBase, nextLength, nextIndex, less⟩ :=
    body_continues source post result base length index hbase hlength hindex execution continues
  constructor
  · exact ⟨index + 1, nextBase, nextLength, nextIndex⟩
  · simp only [remaining, decClock, nextIndex, hindex]
    have bounded := length.isLt
    have smaller : index.toNat < length.toNat := less
    have nowrap : index.toNat + (1 : BitVec 64).toNat < 2 ^ 64 := by
      change index.toNat + 1 < 2 ^ 64
      omega
    rw [BitVec.toNat_add_of_lt nowrap]
    change length.toNat - (index.toNat + 1) < length.toNat - index.toNat
    omega

/-- Actual final memzero byte loop: at most 29 credits per remaining byte,
plus one final body execution. This is a conditional entry bound, not yet a
whole memzero or whole-guest bound. -/
theorem loop_work {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index)) :
    Work (.loop body) source ((length.toNat - index.toNat + 1) * 29) := by
  have bound := loopWorkOfRank body (invariant base length) (remaining length) 29
    (fun state _ => body_work state)
    (fun state post result valid execution continues _ =>
      body_decreases base length state post result valid execution continues)
    source ⟨index, hbase, hlength, hindex⟩
  simpa only [remaining, hindex] using bound

/-- The same rank bounds consumed Stack clock, retaining unused final clock. -/
theorem loop_clock {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index)) :
    source.clock ≤ (evaluate (.loop body, source)).2.clock +
      (length.toNat - index.toNat + 1) * 3 := by
  have bound := loopClockOfRank body (invariant base length) (remaining length) 2
    (fun state _ => body_clock state)
    (fun state post result valid execution continues _ =>
      body_decreases base length state post result valid execution continues)
    source ⟨index, hbase, hlength, hindex⟩
  simpa only [remaining, hindex] using bound

end InitECandidate.Solver.GuestWork.MemzeroTail
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_decreases
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.loop_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.loop_clock

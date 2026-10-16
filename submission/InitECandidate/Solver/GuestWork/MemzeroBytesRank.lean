import InitECandidate.Solver.GuestWork.MemzeroBytes
import InitECandidate.Solver.FlattenWeighted.LoopExit

namespace InitECandidate.Solver.GuestWork.MemzeroBytes
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps
open InitECandidate.Solver.FlattenWeighted

def invariant {C F : Type} (base length : BitVec 64)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  ∃ index : BitVec 64,
    state.regs.lookup 10 = some (.word base) ∧
    state.regs.lookup 11 = some (.word length) ∧
    state.regs.lookup 12 = some (.word index) ∧ index.toNat ≤ length.toNat

def remainingWords {C F : Type} (length : BitVec 64)
    (state : StackSemStateFiniteExact 64 C F) : Nat :=
  match state.regs.lookup 12 with
  | some (.word index) => (length.toNat - index.toNat) / 8
  | _ => 0

private theorem nextIndexNat (length index : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64) (indexBound : index.toNat ≤ length.toNat) :
    (index + 8#64).toNat = index.toNat + 8 := by
  apply BitVec.toNat_add_of_lt
  change index.toNat + 8 < 2 ^ 64
  omega

theorem body_decreases {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64)
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (valid : invariant base length source)
    (execution : evaluate (body, source) = (result, post))
    (continues : StackSemControl.contLoop result = true) :
    invariant base length (decClock post) ∧
      remainingWords length (decClock post) < remainingWords length source := by
  obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
  obtain ⟨nextBase, nextLength, nextIndex, enough⟩ :=
    (body_outcome source post result base length index hbase hlength hindex execution).1 continues
  have nextNat := nextIndexNat length index bounded indexBound
  have enoughNat : (index + 8#64).toNat ≤ length.toNat := enough
  constructor
  · exact ⟨index + 8#64, nextBase, nextLength, nextIndex, enoughNat⟩
  · simp only [remainingWords, decClock, nextIndex, hindex, nextNat]
    omega

/-- Normal exit leaves fewer than eight bytes, with base, length and in-range
index preserved. This postcondition composes with the following byte loops. -/
theorem loop_exit {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64)
    (source post : StackSemStateFiniteExact 64 C F)
    (valid : invariant base length source)
    (execution : evaluate (.loop body, source) = (none, post)) :
    ∃ index : BitVec 64,
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word index) ∧
      index.toNat ≤ length.toNat ∧ length.toNat - index.toNat < 8 := by
  apply loopNormalExit body (invariant base length) _ _ _ source post valid execution
  · intro state next result valid run continues _
    exact (body_decreases base length bounded state next result valid run continues).1
  · intro state next valid run
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    obtain ⟨nextBase, nextLength, nextIndex, stopped⟩ :=
      (body_outcome state next (some (.break 0)) base length index hbase hlength hindex run).2 rfl
    have nextNat := nextIndexNat length index bounded indexBound
    have stoppedNat : length.toNat < (index + 8#64).toNat := stopped
    exact ⟨index, nextBase, nextLength, nextIndex, indexBound, by omega⟩

theorem loop_work {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (indexBound : index.toNat ≤ length.toNat) :
    Work (.loop body) source (((length.toNat - index.toNat) / 8 + 1) * 85) := by
  have bound := loopWorkOfRank body (invariant base length) (remainingWords length) 85
    (fun state _ => body_work state)
    (fun state post result valid execution continues _ =>
      body_decreases base length bounded state post result valid execution continues)
    source ⟨index, hbase, hlength, hindex, indexBound⟩
  simpa only [remainingWords, hindex] using bound

theorem loop_clock {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (base length index : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (indexBound : index.toNat ≤ length.toNat) :
    source.clock ≤ (evaluate (.loop body, source)).2.clock +
      ((length.toNat - index.toNat) / 8 + 1) * 3 := by
  have bound := loopClockOfRank body (invariant base length) (remainingWords length) 2
    (fun state _ => body_clock state)
    (fun state post result valid execution continues _ =>
      body_decreases base length bounded state post result valid execution continues)
    source ⟨index, hbase, hlength, hindex, indexBound⟩
  simpa only [remainingWords, hindex] using bound

end InitECandidate.Solver.GuestWork.MemzeroBytes
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.body_decreases
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.loop_exit
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.loop_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroBytes.loop_clock

import InitECandidate.Solver.GuestWork.MemzeroLinear
import InitECandidate.Solver.FlattenWeighted.CallClock

namespace InitECandidate.Solver.GuestWork.MemzeroCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound

/-- The actual memzero body cannot raise, even with malformed memory or an
insufficient initial clock. Its caller's exception handler is unreachable. -/
theorem no_exception {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (value : WordLocW 64) : (evaluate (Named78.2, source)).1 ≠ some (.exception value) :=
  noException Named78.2 (by decide) source value

def pre {C F : Type} (base length : BitVec 64) (source : StackSemStateFiniteExact 64 C F) : Prop :=
  sptLookup 78 source.code = some Named78.2 ∧ MemzeroEntry.pre base length source

/-- Returning-call bound including actual return-label installation, call
clock, memzero execution, and a basic compiled return continuation. The
exception handler may be arbitrary because actual memzero never raises. -/
theorem callBound {C F : Type}
    (continuation : HolProg 64) (label offset : Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (supported : basic continuation = true)
    (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F)
      (.call (some (continuation, 1, label, offset)) (.inl 78) handler)
      (pre base length) (fun _ => True)
      (17 * maximumBytes + 447 + (ticks continuation + nodes continuation) + 1)
      (maximumBytes + 44 + ticks continuation) := by
  have calleeBound : BlockBound (C := C) (F := F) Named78.2
      (MemzeroEntry.pre base length) (fun _ => True) (17 * maximumBytes + 447) (maximumBytes + 43) :=
    (MemzeroEntry.entryBound base length (by omega)).weaken (fun _ h => h) (fun _ h => h)
      (by have := MemzeroEntry.workBudget_linear length; omega)
      (by have := MemzeroEntry.consumedBudget_linear length; omega)
  have enter : ∀ source : StackSemStateFiniteExact 64 C F,
      MemzeroEntry.pre base length source →
      MemzeroEntry.pre base length (decClock (setVar 1 (.loc label offset) source)) := by
    intro source valid
    simpa [MemzeroEntry.pre, decClock, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using valid
  constructor
  · intro source valid
    obtain ⟨installed, valid⟩ := valid
    apply Work.returningCall (calleeCredit := 17 * maximumBytes + 447)
      (nextCredit := ticks continuation + nodes continuation)
    · intro _ prog found
      simp only [findCode, installed, Option.some.injEq] at found
      subst prog
      exact calleeBound.work _ (enter source valid)
    · intro _ _ _ _
      exact Work.basic supported
    · intro prog post hp hs hl _ found run
      simp only [findCode, installed, Option.some.injEq] at found
      subst prog
      have impossible := no_exception (decClock (setVar 1 (.loc label offset) source)) (.loc hs hl)
      rw [run] at impossible
      exact (impossible rfl).elim
  · intro source valid
    obtain ⟨installed, valid⟩ := valid
    have bounded := returningCallClock Named78.2 continuation 78 1 label offset handler source
      (maximumBytes + 43) (ticks continuation) installed
      (calleeBound.clock _ (enter source valid)) (no_exception _)
      (fun next _ => basicClock continuation next supported)
    omega
  · intro _ _ _ _
    trivial
  · intro source post valid run
    obtain ⟨installed, valid⟩ := valid
    exact returningCallTimeout Named78.2 continuation 78 1 label offset handler source installed
      (no_exception _) (fun next timeout => calleeBound.timeout _ next (enter source valid) timeout)
      (fun middle next _ timeout => by
        have zero := basicTimeoutClock continuation middle supported
        rw [timeout] at zero
        exact zero rfl) post run

end InitECandidate.Solver.GuestWork.MemzeroCall
#print axioms InitECandidate.Solver.GuestWork.MemzeroCall.no_exception
#print axioms InitECandidate.Solver.GuestWork.MemzeroCall.callBound

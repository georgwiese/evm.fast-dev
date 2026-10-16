import InitECandidate.Solver.GuestWork.FrameAllocBlock
import InitECandidate.Solver.GuestWork.FrameAllocState
import InitECandidate.Solver.FlattenWeighted.CallClock
import InitECandidate.Proofs.BackendStages.Named484

namespace InitECandidate.Solver.GuestWork.FrameAllocCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound

/-- Installed allocator and its concrete ABI/guard facts after actual link
installation. Its Ready predicate is independent of the initial clock. -/
def pre {C F : Type}
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (label returnOffset : Nat) (source : StackSemStateFiniteExact 64 C F) : Prop :=
  sptLookup 71 source.code = some Named71.2 ∧
  FrameAllocEntry.Ready (decClock (setVar 1 (.loc label returnOffset) source))
    metadata offset heap globals stack pointer scratch amount label returnOffset

/-- Actual returning allocator call, including the call clock and basic return
continuation. The guarded callee never reaches the exception handler. -/
theorem call_bound {C F : Type}
    (continuation : HolProg 64) (label returnOffset : Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (supported : basic continuation = true)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64) :
    BlockBound (C := C) (F := F)
      (.call (some (continuation, 1, label, returnOffset)) (.inl 71) handler)
      (pre metadata offset heap globals stack pointer scratch amount label returnOffset)
      (fun _ => True) (59 + ticks continuation + nodes continuation) (5 + ticks continuation) := by
  have callee := FrameAllocEntry.entry_bound (C := C) (F := F)
    metadata offset heap globals stack pointer scratch amount label returnOffset
  constructor
  · intro source valid
    have noRaise := FrameAllocEntry.no_exception _ metadata offset heap globals stack pointer scratch amount
      label returnOffset valid.2
    apply Work.mono (first := 58 + (ticks continuation + nodes continuation) + 1) (by omega)
    apply Work.returningCall (calleeCredit := 58) (nextCredit := ticks continuation + nodes continuation)
    · intro _ prog found
      simp only [findCode, valid.1, Option.some.injEq] at found
      subst prog
      exact callee.work _ valid.2
    · intro _ _ _ _
      exact Work.basic supported
    · intro prog post hp hs hl _ found run
      simp only [findCode, valid.1, Option.some.injEq] at found
      subst prog
      have impossible := noRaise (.loc hs hl)
      rw [run] at impossible
      exact (impossible rfl).elim
  · intro source valid
    have noRaise := FrameAllocEntry.no_exception _ metadata offset heap globals stack pointer scratch amount
      label returnOffset valid.2
    have clock := returningCallClock Named71.2 continuation 71 1 label returnOffset handler source 4
      (ticks continuation) valid.1 (callee.clock _ valid.2) noRaise
      (fun next _ => basicClock continuation next supported)
    omega
  · intro _ _ _ _
    trivial
  · intro source post valid run
    have noRaise := FrameAllocEntry.no_exception _ metadata offset heap globals stack pointer scratch amount
      label returnOffset valid.2
    exact returningCallTimeout Named71.2 continuation 71 1 label returnOffset handler source valid.1 noRaise
      (fun next timedOut => callee.timeout _ next valid.2 timedOut)
      (fun middle next _ timedOut => by
        have zero := basicTimeoutClock continuation middle supported
        rw [timedOut] at zero
        exact zero rfl) post run

/-- The actual allocator call in extend_memory, including continuation116. -/
theorem extend_memory_call_bound {C F : Type}
    (metadata offset heap globals stack pointer scratch amount : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody484_134
      (pre metadata offset heap globals stack pointer scratch amount 484 2)
      (fun _ => True) 82 5 :=
  call_bound NamedBody484_116 484 2 (some (NamedBody484_133, 484, 3)) (by decide)
    metadata offset heap globals stack pointer scratch amount

end InitECandidate.Solver.GuestWork.FrameAllocCall
#print axioms InitECandidate.Solver.GuestWork.FrameAllocCall.call_bound
#print axioms InitECandidate.Solver.GuestWork.FrameAllocCall.extend_memory_call_bound

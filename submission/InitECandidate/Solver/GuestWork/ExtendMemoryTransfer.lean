import InitECandidate.Solver.GuestWork.ExtendMemoryCalls
import InitECandidate.Solver.GuestWork.ExtendMemoryRestore

namespace InitECandidate.Solver.GuestWork.ExtendMemoryTransfer
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Call-entry arguments plus a bound on the separately saved logical extension.
The cleared capacity length and saved logical length need not be equal. -/
def beforeCall {C F : Type} (base clearLength stack metadata : BitVec 64) (savedMaximum : Nat)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  MemzeroCall.pre base clearLength state ∧
  state.regs.lookup 24 = some (.word stack) ∧
  state.regs.lookup 25 = some (.word metadata) ∧
  ∃ value, state.memory (stack + 24#64 + 32#64) = .word value ∧ value.toNat ≤ savedMaximum

def afterCall {C F : Type} (stack metadata : BitVec 64) (savedMaximum : Nat)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  sptLookup 78 state.code = some Named78.2 ∧
  state.regs.lookup 24 = some (.word (stack + 24#64)) ∧
  state.regs.lookup 25 = some (.word metadata) ∧
  ∃ value, state.regs.lookup 11 = some (.word value) ∧ value.toNat ≤ savedMaximum

/-- Strengthen the actual capacity-clearing call's cost contract with the
saved-length and restored-stack postcondition needed by the second call. -/
theorem capacity_call_bound {C F : Type}
    (base clearLength stack metadata : BitVec 64) (clearMaximum savedMaximum : Nat)
    (clearBound : clearLength.toNat ≤ clearMaximum) (maximumBound : clearMaximum + 32 < 2 ^ 64)
    (separated : stack + 24#64 + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_214
      (beforeCall base clearLength stack metadata savedMaximum) (afterCall stack metadata savedMaximum)
      (17 * clearMaximum + 465) (clearMaximum + 44) := by
  have cost := ExtendMemoryCalls.capacityCallBound (C := C) (F := F)
    base clearLength clearMaximum clearBound maximumBound
  constructor
  · intro source valid
    exact cost.work source valid.1
  · intro source valid
    exact cost.clock source valid.1
  · intro source post valid run
    obtain ⟨callee, hstack, hmetadata, bounded⟩ := valid
    have transferred := ExtendMemoryRestore.capacity_call_saved_length source post stack metadata
      savedMaximum callee.1 hstack hmetadata bounded separated run
    refine ⟨?_, transferred.2.2.1, transferred.2.2.2, transferred.1⟩
    rw [transferred.2.1]
    exact callee.1
  · intro source post valid run
    exact cost.timeout source post valid.1 run

/-- The actual following EV_MEM_CAP store retains the restored register bound
and call-entry metadata on every normal exit. Memory validity is not assumed. -/
theorem capacity_tail_bound {C F : Type} (stack metadata : BitVec 64) (savedMaximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_236
      (afterCall stack metadata savedMaximum) (afterCall stack metadata savedMaximum) 18 1 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  obtain ⟨installed, hstack, hmetadata, value, found, small⟩ := valid
  have lengthFrame := normalFrame NamedBody484_236 11 (by decide) source post run
  have stackFrame := normalFrame NamedBody484_236 24 (by decide) source post run
  have metadataFrame := normalFrame NamedBody484_236 25 (by decide) source post run
  refine ⟨?_, stackFrame.1.trans hstack, metadataFrame.1.trans hmetadata,
    value, lengthFrame.1.trans found, small⟩
  rw [lengthFrame.2]
  exact installed

end InitECandidate.Solver.GuestWork.ExtendMemoryTransfer
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryTransfer.capacity_call_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryTransfer.capacity_tail_bound

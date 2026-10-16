import InitECandidate.Solver.GuestWork.FrameAllocAllClocks

namespace InitECandidate.Solver.GuestWork.FrameAllocEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Under the actual allocator guards, every run returns to its caller or
runs out of clock. No normal fall-through or exception handler is reachable. -/
theorem outcome {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (valid : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (run : evaluate (Named71.2, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∨
      (result = some .timeOut ∧ post.clock = 0) := by
  by_cases enough : 4 ≤ source.clock
  · left
    exact (updates source post result metadata offset heap globals stack pointer scratch amount
      returnLabel returnOffset valid.hmetadata valid.hheap valid.hstack valid.hamount valid.hreturn
      valid.stackSafe valid.metadataDomain valid.metadataValue valid.globalsEq valid.pointerDomain
      valid.pointerValue valid.scratchDomain valid.scratchValue valid.saveDomain valid.metadataNotSave
      valid.scratchNotSave valid.fits valid.roundedFits enough run).1
  · right
    have timedOut := small_timeout source metadata offset heap globals stack pointer scratch amount
      returnLabel returnOffset valid (by omega)
    simpa only [run] using timedOut

theorem no_exception {C F : Type}
    (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (valid : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (value : WordLocW 64) : (evaluate (Named71.2, source)).1 ≠ some (.exception value) := by
  rcases run : evaluate (Named71.2, source) with ⟨result, post⟩
  have choices := outcome source post result metadata offset heap globals stack pointer scratch amount
    returnLabel returnOffset valid run
  rcases choices with returned | ⟨timedOut, _⟩
  · simp [returned]
  · simp [timedOut]

/-- Composable bound for actual frame_mem_alloc under its entry ABI and guards,
including runs that start with fewer than four clock units. -/
theorem entry_bound {C F : Type}
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat) :
    BlockBound (C := C) (F := F) Named71.2
      (fun source => Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
      (fun _ => False) 58 4 := by
  constructor
  · intro source valid
    exact work_all_clocks source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset
      valid.hmetadata valid.hheap valid.hstack valid.hamount valid.hreturn valid.stackSafe
      valid.metadataDomain valid.metadataValue valid.globalsEq valid.pointerDomain valid.pointerValue
      valid.scratchDomain valid.scratchValue valid.saveDomain valid.metadataNotSave valid.scratchNotSave
      valid.fits valid.roundedFits
  · intro source valid
    by_cases enough : 4 ≤ source.clock
    · rcases run : evaluate (Named71.2, source) with ⟨result, post⟩
      have summary := updates source post result metadata offset heap globals stack pointer scratch amount
        returnLabel returnOffset valid.hmetadata valid.hheap valid.hstack valid.hamount valid.hreturn
        valid.stackSafe valid.metadataDomain valid.metadataValue valid.globalsEq valid.pointerDomain
        valid.pointerValue valid.scratchDomain valid.scratchValue valid.saveDomain valid.metadataNotSave
        valid.scratchNotSave valid.fits valid.roundedFits enough run
      have clock := summary.2.2.2.2.2.2.1
      dsimp only
      omega
    · omega
  · intro source post valid run
    have choices := outcome source post none metadata offset heap globals stack pointer scratch amount
      returnLabel returnOffset valid run
    rcases choices with returned | ⟨timedOut, _⟩ <;> contradiction
  · intro source post valid run
    have choices := outcome source post (some .timeOut) metadata offset heap globals stack pointer scratch amount
      returnLabel returnOffset valid run
    rcases choices with returned | ⟨_, zero⟩
    · simp at returned
    · exact zero

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.outcome
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.no_exception
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.entry_bound

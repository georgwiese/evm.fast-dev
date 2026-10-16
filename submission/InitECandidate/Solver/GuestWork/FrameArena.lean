import InitECandidate.Solver.GuestWork.FrameAllocBounded
import InitECandidate.Solver.GuestWork.MemzeroLinear

namespace InitECandidate.Solver.GuestWork.FrameArena
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Fixed scratch/frame arena constants from the guest configuration. Global
initialization and preservation of these limits are still caller obligations. -/
def arenaStart : Nat := 2701135872
def arenaEnd : Nat := 2713714688
def arenaBytes : Nat := 12578816

theorem request_bound (pointer scratch amount : BitVec 64)
    (pointerLower : arenaStart ≤ pointer.toNat)
    (pointerOrdered : pointer ≤ scratch)
    (scratchUpper : scratch.toNat ≤ arenaEnd)
    (fits : ¬ scratch - pointer < amount) : amount.toNat ≤ arenaBytes := by
  have subtract := BitVec.toNat_sub_of_le pointerOrdered
  change ¬ (scratch - pointer).toNat < amount.toNat at fits
  dsimp [arenaStart, arenaEnd, arenaBytes] at *
  omega

/-- Clearing the low three bits gives the exact rounded-down multiple of eight. -/
theorem mask_toNat (value : BitVec 64) :
    (value &&& 18446744073709551608#64).toNat = value.toNat / 8 * 8 := by
  have small := value.isLt
  have divEq : (value.toNat &&& 18446744073709551608) / 8 = value.toNat / 8 := by
    calc
      _ = value.toNat / 8 &&& (2 ^ 61 - 1) := Nat.and_div_two_pow (n := 3)
      _ = value.toNat / 8 := Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have modEq : (value.toNat &&& 18446744073709551608) % 8 = 0 := by
    calc
      _ = (value.toNat % 8) &&& 0 := Nat.and_mod_two_pow (n := 3)
      _ = 0 := Nat.and_zero _
  change value.toNat &&& 18446744073709551608 = value.toNat / 8 * 8
  omega

/-- The pointer arithmetic on the actual success path reserves the requested
bytes and at most seven padding bytes, provided the addition cannot wrap. -/
theorem rounded_bounds (pointer amount : BitVec 64)
    (noWrap : amount.toNat + pointer.toNat + 7 < 2 ^ 64) :
    let next := (amount + pointer + 7#64) &&& 18446744073709551608#64
    pointer.toNat + amount.toNat ≤ next.toNat ∧
    next.toNat < pointer.toNat + amount.toNat + 8 ∧ next.toNat % 8 = 0 := by
  have sumNat : (amount + pointer).toNat = amount.toNat + pointer.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have nextNat : (amount + pointer + 7#64).toNat = amount.toNat + pointer.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by rw [sumNat]; exact noWrap), sumNat]
    rfl
  dsimp only
  rw [mask_toNat, nextNat]
  omega

/-- For an actual successful allocator execution in the arena, the stored
pointer covers the request, stays below scratch, and is eight-byte aligned. -/
theorem allocate_in_arena {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (ready : FrameAllocEntry.Ready source metadata offset heap globals stack
      pointer scratch amount returnLabel returnOffset)
    (pointerLower : arenaStart ≤ pointer.toNat)
    (pointerOrdered : pointer ≤ scratch)
    (scratchUpper : scratch.toNat ≤ arenaEnd)
    (enoughClock : 4 ≤ source.clock)
    (execution : evaluate (Named71.2, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∧
    post.regs.lookup 10 = some (.word pointer) ∧
    post.clock = source.clock - 4 ∧
    ∃ next : BitVec 64,
      post.memory (globals + 18446744073709551584#64) = .word next ∧
      pointer.toNat + amount.toNat ≤ next.toNat ∧
      next.toNat ≤ scratch.toNat ∧
      next.toNat < pointer.toNat + amount.toNat + 8 ∧
      next.toNat % 8 = 0 ∧ amount.toNat ≤ arenaBytes := by
  have subtract := BitVec.toNat_sub_of_le pointerOrdered
  have fits := ready.fits
  change ¬ (scratch - pointer).toNat < amount.toNat at fits
  have ordered : pointer.toNat ≤ scratch.toNat := pointerOrdered
  have noWrap : amount.toNat + pointer.toNat + 7 < 2 ^ 64 := by
    dsimp [arenaEnd] at scratchUpper
    omega
  have rounded := rounded_bounds pointer amount noWrap
  have belowScratch :
      ((amount + pointer + 7#64) &&& 18446744073709551608#64).toNat ≤ scratch.toNat := by
    have h := ready.roundedFits
    change ¬ scratch.toNat < _ at h
    omega
  have update := FrameAllocEntry.updates source post result
    metadata offset heap globals stack pointer scratch amount returnLabel returnOffset
    ready.hmetadata ready.hheap ready.hstack ready.hamount ready.hreturn ready.stackSafe ready.metadataDomain ready.metadataValue ready.globalsEq ready.pointerDomain ready.pointerValue ready.scratchDomain ready.scratchValue ready.saveDomain ready.metadataNotSave ready.scratchNotSave ready.fits ready.roundedFits
    enoughClock execution
  rcases update with ⟨returned, returnReg, _, stored, _, _, clock, _⟩
  exact ⟨returned, returnReg, clock, _, stored, rounded.1, belowScratch,
    rounded.2.1, rounded.2.2,
    request_bound pointer scratch amount pointerLower pointerOrdered scratchUpper ready.fits⟩

/-- A successful size check in this arena supplies the concrete maximum needed
by the already checked memzero summary. This does not bound persistent-heap or
other memzero callers. -/
theorem bounded_memzero {C F : Type}
    (allocationSource source post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (ready : FrameAllocEntry.Ready allocationSource metadata offset heap globals stack
      pointer scratch amount returnLabel returnOffset)
    (pointerLower : arenaStart ≤ pointer.toNat)
    (pointerOrdered : pointer ≤ scratch)
    (scratchUpper : scratch.toNat ≤ arenaEnd)
    (hbase : source.regs.lookup 10 = some (.word pointer))
    (hlength : source.regs.lookup 11 = some (.word amount))
    (execution : evaluate (Named78.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named78.2, {source with clock := 12578860}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named78.2 {source with clock := 12578860} 213840319 := by
  exact MemzeroEntry.bounded_execution_linear source post result pointer amount arenaBytes
    (request_bound pointer scratch amount pointerLower pointerOrdered scratchUpper ready.fits)
    (by decide) hbase hlength execution notTimeout

end InitECandidate.Solver.GuestWork.FrameArena
#print axioms InitECandidate.Solver.GuestWork.FrameArena.request_bound
#print axioms InitECandidate.Solver.GuestWork.FrameArena.mask_toNat
#print axioms InitECandidate.Solver.GuestWork.FrameArena.rounded_bounds
#print axioms InitECandidate.Solver.GuestWork.FrameArena.bounded_memzero

#print axioms InitECandidate.Solver.GuestWork.FrameArena.allocate_in_arena

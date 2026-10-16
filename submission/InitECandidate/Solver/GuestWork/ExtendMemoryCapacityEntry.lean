import InitECandidate.Solver.GuestWork.ExtendMemoryBlock
import InitECandidate.Solver.GuestWork.ExtendMemoryLength
import InitECandidate.Solver.FlattenWeighted.BlockPrefix

namespace InitECandidate.Solver.GuestWork.ExtendMemoryCapacityEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Concrete state immediately after the allocator call restores its caller.
The saved logical extension and the capacity increase have separate bounds. -/
structure Ready {C F : Type} (savedMaximum : Nat)
    (nextCapacity capacity stack metadata offset heap frame memoryBase : BitVec 64)
    (source : StackSemStateFiniteExact 64 C F) : Prop where
  installed : sptLookup 78 source.code = some Named78.2
  hnextCapacity : source.regs.lookup 1 = some (.word nextCapacity)
  hcapacity : source.regs.lookup 11 = some (.word capacity)
  hstack : source.regs.lookup 24 = some (.word stack)
  hmetadata : source.regs.lookup 25 = some (.word metadata)
  hheap : source.regs.lookup 26 = some (.word heap)
  saved : ∃ value, source.memory (stack + 32#64) = .word value ∧ value.toNat ≤ savedMaximum
  metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true
  metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset
  frameDomain : source.mdomain ((offset <<< (1 : Nat)) + heap + 18446744073709551360#64) = true
  frameValue : source.memory ((offset <<< (1 : Nat)) + heap + 18446744073709551360#64) = .word frame
  baseDomain : source.mdomain (frame + 24#64) = true
  baseValue : source.memory (frame + 24#64) = .word memoryBase

def setupBlocks : List (HolProg 64) := [NamedBody484_140, NamedBody484_141, NamedBody484_142, NamedBody484_143, NamedBody484_144, NamedBody484_145, NamedBody484_146, NamedBody484_147, NamedBody484_148, NamedBody484_149, NamedBody484_150]

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

theorem setup_transfer {C F : Type} (savedMaximum : Nat)
    (nextCapacity capacity stack metadata offset heap frame memoryBase : BitVec 64)
    (source post : StackSemStateFiniteExact 64 C F)
    (valid : Ready savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase source)
    (run : evaluate (prefixChain setupBlocks .skip, source) = (none, post)) :
    ExtendMemoryBlock.beforeBlock (capacity + memoryBase) (nextCapacity - capacity) stack metadata savedMaximum post := by
  obtain ⟨installed, hnextCapacity, hcapacity, hstack, hmetadata, hheap,
    saved, metadataDomain, metadataValue, frameDomain, frameValue, baseDomain, baseValue⟩ := valid
  obtain ⟨value, found, small⟩ := saved
  have separated : stack + 32#64 ≠ stack + 16#64 := by simp
  by_cases zero : source.clock = 0 <;> by_cases saveDomain : source.mdomain (stack + 16#64) = true
  all_goals
    simp [setupBlocks, prefixChain, NamedBody484_140, NamedBody484_141, NamedBody484_142, NamedBody484_143, NamedBody484_144, NamedBody484_145, NamedBody484_146, NamedBody484_147, NamedBody484_148, NamedBody484_149, NamedBody484_150,
      seqEvaluate, evaluate_skip, evaluate_inst, evaluate_tick, StackSemInst.instHOL,
      instInteger, assign, wordExp, wordOpHOL, wordOp, wordShiftHOL, memLoad, memStore,
      StackSemStateOps.getVar, setVar, decClock, hnextCapacity, hcapacity, hstack, hmetadata,
      hheap, metadataDomain, metadataValue, frameDomain, frameValue, baseDomain, baseValue,
      zero, saveDomain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run
  all_goals
    subst post
    refine ⟨⟨installed, ?_, ?_⟩, ?_, ?_, value, ?_, small⟩ <;>
      simp [setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, separated, found, hstack, hmetadata]

/-- Actual growth suffix248 after allocator return: compute both memzero
arguments, save capacity, zero the added capacity and store EV_MEM_CAP. -/
theorem capacity_bound {C F : Type} (clearMaximum savedMaximum : Nat)
    (nextCapacity capacity stack metadata offset heap frame memoryBase : BitVec 64)
    (clearBound : (nextCapacity - capacity).toNat ≤ clearMaximum)
    (maximumBound : clearMaximum + 32 < 2 ^ 64)
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_248
      (Ready savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase)
      (ExtendMemoryTransfer.afterCall (stack - 24#64) metadata savedMaximum)
      (17 * clearMaximum + 529) (clearMaximum + 46) := by
  have combined := BlockBound.basicPrefix (C := C) (F := F) setupBlocks NamedBody484_237
    (Ready savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase)
    (ExtendMemoryBlock.beforeBlock (capacity + memoryBase) (nextCapacity - capacity) stack metadata savedMaximum)
    (ExtendMemoryTransfer.afterCall (stack - 24#64) metadata savedMaximum)
    (17 * clearMaximum + 517) (clearMaximum + 45)
    (by intro prog member; simp only [setupBlocks, List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with h | h | h | h | h | h | h | h | h | h | h <;> subst prog <;> decide)
    (setup_transfer savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase)
    (ExtendMemoryBlock.capacity_suffix_bound (capacity + memoryBase) (nextCapacity - capacity)
      stack metadata clearMaximum savedMaximum clearBound maximumBound separated)
  apply combined.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [prefixCredits, prefixClocks, setupBlocks, ticks, nodes, NamedBody484_140, NamedBody484_141, NamedBody484_142, NamedBody484_143, NamedBody484_144, NamedBody484_145, NamedBody484_146, NamedBody484_147, NamedBody484_148, NamedBody484_149, NamedBody484_150] <;> omega

theorem capacity_to_length {C F : Type} (clearMaximum savedMaximum : Nat)
    (nextCapacity capacity stack metadata offset heap frame memoryBase : BitVec 64)
    (clearBound : (nextCapacity - capacity).toNat ≤ clearMaximum)
    (maximumBound : clearMaximum + 32 < 2 ^ 64)
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_248
      (Ready savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase)
      (ExtendMemoryLength.lengthReady savedMaximum)
      (17 * clearMaximum + 529) (clearMaximum + 46) :=
  (capacity_bound clearMaximum savedMaximum nextCapacity capacity stack metadata offset heap frame memoryBase
    clearBound maximumBound separated).weaken (fun _ h => h)
    (fun state valid => ExtendMemoryLength.after_capacity_ready state (stack - 24#64) metadata savedMaximum valid)
    (by omega) (by omega)

end InitECandidate.Solver.GuestWork.ExtendMemoryCapacityEntry
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCapacityEntry.setup_transfer
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCapacityEntry.capacity_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCapacityEntry.capacity_to_length

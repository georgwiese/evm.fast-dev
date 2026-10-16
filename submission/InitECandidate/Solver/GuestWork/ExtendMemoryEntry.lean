import InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth
import InitECandidate.Solver.FlattenWeighted.BlockPrefix

namespace InitECandidate.Solver.GuestWork.ExtendMemoryEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Entry ABI and the actual memory cells used to select a nonzero extension
within existing capacity. These are source-state facts, not execution bounds. -/
structure Ready {C F : Type} (maximum : Nat)
    (amount stack metadata offset heap frame oldLength capacity : BitVec 64)
    (source : StackSemStateFiniteExact 64 C F) : Prop where
  installed : sptLookup 78 source.code = some Named78.2
  hamount : source.regs.lookup 10 = some (.word amount)
  hstack : source.regs.lookup 24 = some (.word stack)
  hmetadata : source.regs.lookup 25 = some (.word metadata)
  hheap : source.regs.lookup 26 = some (.word heap)
  nonzero : amount ≠ 0#64
  small : amount.toNat ≤ maximum
  stackSafe : ¬stack - 56#64 < metadata
  metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true
  metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset
  frameDomain : source.mdomain ((offset <<< (1 : Nat)) + heap + 18446744073709551360#64) = true
  frameValue : source.memory ((offset <<< (1 : Nat)) + heap + 18446744073709551360#64) = .word frame
  lengthDomain : source.mdomain (frame + 32#64) = true
  lengthValue : source.memory (frame + 32#64) = .word oldLength
  capacityDomain : source.mdomain (frame + 40#64) = true
  capacityValue : source.memory (frame + 40#64) = .word capacity
  enoughCapacity : ¬capacity < amount + oldLength

def entryBlocks : List (HolProg 64) := [NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_19, NamedBody484_20, NamedBody484_21, NamedBody484_22, NamedBody484_23, NamedBody484_24, NamedBody484_25, NamedBody484_26, NamedBody484_27, NamedBody484_28, NamedBody484_29, NamedBody484_30, NamedBody484_31]

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

theorem entry_transfer {C F : Type} (maximum : Nat)
    (amount stack metadata offset heap frame oldLength capacity : BitVec 64)
    (source post : StackSemStateFiniteExact 64 C F)
    (valid : Ready maximum amount stack metadata offset heap frame oldLength capacity source)
    (run : evaluate (prefixChain entryBlocks .skip, source) = (none, post)) :
    ExtendMemoryNoGrowth.ready maximum post := by
  obtain ⟨installed, hamount, hstack, hmetadata, hheap, nonzero, small, stackSafe,
    metadataDomain, metadataValue, frameDomain, frameValue, lengthDomain, lengthValue,
    capacityDomain, capacityValue, enoughCapacity⟩ := valid
  have nonzeroTest : (amount == 0#64) = false := beq_eq_false_iff_ne.mpr nonzero
  by_cases zero : source.clock = 0 <;> by_cases one : source.clock - 1 = 0
  all_goals
    simp [entryBlocks, prefixChain, NamedBody484_0, NamedBody484_1, NamedBody484_2, NamedBody484_3, NamedBody484_4, NamedBody484_5, NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_9, NamedBody484_10, NamedBody484_11, NamedBody484_12, NamedBody484_13, NamedBody484_14, NamedBody484_15, NamedBody484_16, NamedBody484_17, NamedBody484_18, NamedBody484_19, NamedBody484_20, NamedBody484_21, NamedBody484_22, NamedBody484_23, NamedBody484_24, NamedBody484_25, NamedBody484_26, NamedBody484_27, NamedBody484_28, NamedBody484_29, NamedBody484_30, NamedBody484_31,
      seqEvaluate, evaluate_skip, evaluate_inst, evaluate_tick, evaluate_ite,
      evaluate_ret, evaluate_halt, StackSemInst.instHOL, instInteger, assign,
      wordExp, wordOpHOL, wordOp, wordShiftHOL, memLoad,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      wordSemWordCmp, wordCmpHOL, setVar, decClock, hamount, hstack, hmetadata, hheap,
      nonzero, nonzeroTest, stackSafe, metadataDomain, metadataValue, frameDomain, frameValue,
      lengthDomain, lengthValue, capacityDomain, capacityValue, zero, one,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run
  all_goals
    subst post
    refine ⟨⟨installed, amount, ?_, small⟩, capacity, amount + oldLength, ?_, ?_, enoughCapacity⟩ <;>
      simp [setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Whole actual extend_memory for a nonzero extension that fits the current
capacity, including its entry prologue, lookups and final call/store/return. -/
theorem entry_bound {C F : Type} (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64)
    (amount stack metadata offset heap frame oldLength capacity : BitVec 64) :
    BlockBound (C := C) (F := F) Named484.2
      (Ready maximum amount stack metadata offset heap frame oldLength capacity) (fun _ => True)
      (17 * maximum + 569) (maximum + 50) := by
  have combined := BlockBound.basicPrefix (C := C) (F := F) entryBlocks NamedBody484_364
    (Ready maximum amount stack metadata offset heap frame oldLength capacity)
    (ExtendMemoryNoGrowth.ready maximum) (fun _ => True)
    (17 * maximum + 534) (maximum + 47)
    (by intro prog member; simp only [entryBlocks, List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst prog <;> decide)
    (entry_transfer maximum amount stack metadata offset heap frame oldLength capacity)
    (ExtendMemoryNoGrowth.suffix_bound maximum maximumBound)
  apply combined.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [prefixCredits, prefixClocks, entryBlocks, ticks, nodes, NamedBody484_0, NamedBody484_1, NamedBody484_2, NamedBody484_3, NamedBody484_4, NamedBody484_5, NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_9, NamedBody484_10, NamedBody484_11, NamedBody484_12, NamedBody484_13, NamedBody484_14, NamedBody484_15, NamedBody484_16, NamedBody484_17, NamedBody484_18, NamedBody484_19, NamedBody484_20, NamedBody484_21, NamedBody484_22, NamedBody484_23, NamedBody484_24, NamedBody484_25, NamedBody484_26, NamedBody484_27, NamedBody484_28, NamedBody484_29, NamedBody484_30, NamedBody484_31] <;> omega

theorem bounded_entry {C F : Type} (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64)
    (amount stack metadata offset heap frame oldLength capacity : BitVec 64)
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (valid : Ready maximum amount stack metadata offset heap frame oldLength capacity source)
    (run : evaluate (Named484.2, source) = (result, post)) (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named484.2, {source with clock := maximum + 51}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named484.2 {source with clock := maximum + 51} (17 * maximum + 569) := by
  apply (entry_bound maximum maximumBound amount stack metadata offset heap frame oldLength capacity).boundedExecution
    (by
      intro state clock h
      exact ⟨h.installed, h.hamount, h.hstack, h.hmetadata, h.hheap, h.nonzero, h.small,
        h.stackSafe, h.metadataDomain, h.metadataValue, h.frameDomain, h.frameValue,
        h.lengthDomain, h.lengthValue, h.capacityDomain, h.capacityValue, h.enoughCapacity⟩) source post result valid run notTimeout

end InitECandidate.Solver.GuestWork.ExtendMemoryEntry
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryEntry.entry_transfer
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryEntry.entry_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryEntry.bounded_entry

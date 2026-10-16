import InitECandidate.Solver.GuestWork.MemzeroCall
import InitECandidate.Solver.FlattenWeighted.BasicFrame
import InitECandidate.Solver.FlattenWeighted.BlockIf
import InitECandidate.Proofs.BackendStages.Named484

namespace InitECandidate.Solver.GuestWork.ExtendMemoryCalls
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- First actual memzero call site: zero newly allocated capacity. -/
theorem capacityCallBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_214 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 465) (maximumBytes + 44) := by
  have t : ticks NamedBody484_202 = 0 := by decide
  have n : nodes NamedBody484_202 = 17 := by decide
  simpa only [NamedBody484_214, NamedBody484_325, t, n, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
    (MemzeroCall.callBound (C := C) (F := F) NamedBody484_202 484 4 (some (NamedBody484_213, 484, 5))
      (by decide) base length maximumBytes lengthBound maximumBound)

/-- Second actual memzero call site: zero the logical memory extension. -/
theorem lengthCallBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_325 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 459) (maximumBytes + 44) := by
  have t : ticks NamedBody484_319 = 0 := by decide
  have n : nodes NamedBody484_319 = 11 := by decide
  simpa only [NamedBody484_214, NamedBody484_325, t, n, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using
    (MemzeroCall.callBound (C := C) (F := F) NamedBody484_319 484 6 (some (NamedBody484_324, 484, 7))
      (by decide) base length maximumBytes lengthBound maximumBound)

private theorem preservingBound {C F : Type} (prog : HolProg 64)
    (base length : BitVec 64) (supported : basic prog = true)
    (baseSafe : keepsReg 10 prog = true) (lengthSafe : keepsReg 11 prog = true) :
    BlockBound (C := C) (F := F) prog (MemzeroCall.pre base length) (MemzeroCall.pre base length)
      (ticks prog + nodes prog) (ticks prog) := by
  apply BlockBound.basic _ _ _ supported
  intro source post valid run
  have baseFrame := normalFrame prog 10 baseSafe source post run
  have lengthFrame := normalFrame prog 11 lengthSafe source post run
  obtain ⟨installed, hbase, hlength⟩ := valid
  exact ⟨by simpa only [baseFrame.2] using installed,
    baseFrame.1.trans hbase, lengthFrame.1.trans hlength⟩

private theorem haltBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody484_281
      (MemzeroCall.pre base length) (MemzeroCall.pre base length) 3 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post _ run
  rw [NamedBody484_281, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  simp [NamedBody484_279, NamedBody484_280, evaluate_inst, evaluate_halt,
    StackSemInst.instHOL, instInteger, assign, wordExp, setVar, StackSemStateOps.getVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run

private theorem setupBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody484_306
      (MemzeroCall.pre base length) (MemzeroCall.pre base length) 26 0 := by
  have skip := preservingBound (C := C) (F := F) NamedBody484_282 base length (by decide) (by decide) (by decide)
  have branch := BlockBound.ite .lower 24 (.reg 25)
    (haltBound (C := C) (F := F) base length)
    (skip.weaken (fun _ h => h) (fun _ h => h) (by decide) (by decide))
  have prologue := (preservingBound (C := C) (F := F) NamedBody484_278 base length (by decide) (by decide) (by decide)).seq branch
  exact prologue.seq (preservingBound NamedBody484_305 base length (by decide) (by decide) (by decide))

/-- The entire second call block, including saved-handler setup and the actual
return continuation. Invalid setup memory can stop early; valid normal setup
preserves both arguments and the installed memzero code. -/
theorem lengthBlockBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_330 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 493) (maximumBytes + 44) := by
  have final := lengthCallBound (C := C) (F := F) base length maximumBytes lengthBound maximumBound
  have skipA := preservingBound (C := C) (F := F) NamedBody484_308 base length (by decide) (by decide) (by decide)
  have skipB := preservingBound (C := C) (F := F) NamedBody484_307 base length (by decide) (by decide) (by decide)
  have frame := setupBound (C := C) (F := F) base length
  have mark := preservingBound (C := C) (F := F) NamedBody484_277 base length (by decide) (by decide) (by decide)
  have skipC := preservingBound (C := C) (F := F) NamedBody484_274 base length (by decide) (by decide) (by decide)
  have all := skipC.seq (mark.seq (frame.seq (skipB.seq (skipA.seq final))))
  apply all.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [ticks, nodes, NamedBody484_308, NamedBody484_307, NamedBody484_277, NamedBody484_275, NamedBody484_276, NamedBody484_274] <;> omega

/-- Actual suffix from the second call setup through storing the new length
and returning to the caller; no validity assumption is imposed on later loads. -/
theorem suffixBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_354 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 517) (maximumBytes + 45) := by
  have tail : BlockBound (C := C) (F := F) NamedBody484_353 (fun _ => True) (fun _ => True) 24 1 :=
    BlockBound.basic _ _ _ (by decide) (fun _ _ _ _ => trivial)
  have all := (lengthBlockBound (C := C) (F := F) base length maximumBytes lengthBound maximumBound).seq tail
  apply all.weaken (fun _ h => h) (fun _ h => h) <;> omega

theorem bounded_suffix {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64)
    (valid : MemzeroCall.pre base length source)
    (execution : evaluate (NamedBody484_354, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (NamedBody484_354, {source with clock := maximumBytes + 46}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work NamedBody484_354 {source with clock := maximumBytes + 46} (17 * maximumBytes + 517) :=
  (suffixBound base length maximumBytes lengthBound maximumBound).boundedExecution
    (fun _ _ h => h) source post result valid execution notTimeout

private theorem capacityHaltBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody484_158
      (MemzeroCall.pre base length) (MemzeroCall.pre base length) 3 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post _ run
  rw [NamedBody484_158, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  simp [NamedBody484_156, NamedBody484_157, evaluate_inst, evaluate_halt,
    StackSemInst.instHOL, instInteger, assign, wordExp, setVar, StackSemStateOps.getVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run

private theorem capacitySetupBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody484_183
      (MemzeroCall.pre base length) (MemzeroCall.pre base length) 26 0 := by
  have skip := preservingBound (C := C) (F := F) NamedBody484_159 base length (by decide) (by decide) (by decide)
  have branch := BlockBound.ite .lower 24 (.reg 25)
    (capacityHaltBound (C := C) (F := F) base length)
    (skip.weaken (fun _ h => h) (fun _ h => h) (by decide) (by decide))
  have prologue := (preservingBound (C := C) (F := F) NamedBody484_155 base length (by decide) (by decide) (by decide)).seq branch
  exact prologue.seq (preservingBound NamedBody484_182 base length (by decide) (by decide) (by decide))

/-- The entire capacity-clearing call block, including saved-handler setup and the actual
return continuation. Invalid setup memory can stop early; valid normal setup
preserves both arguments and the installed memzero code. -/
theorem capacityBlockBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_219 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 499) (maximumBytes + 44) := by
  have final := capacityCallBound (C := C) (F := F) base length maximumBytes lengthBound maximumBound
  have skipA := preservingBound (C := C) (F := F) NamedBody484_185 base length (by decide) (by decide) (by decide)
  have skipB := preservingBound (C := C) (F := F) NamedBody484_184 base length (by decide) (by decide) (by decide)
  have frame := capacitySetupBound (C := C) (F := F) base length
  have mark := preservingBound (C := C) (F := F) NamedBody484_154 base length (by decide) (by decide) (by decide)
  have skipC := preservingBound (C := C) (F := F) NamedBody484_151 base length (by decide) (by decide) (by decide)
  have all := skipC.seq (mark.seq (frame.seq (skipB.seq (skipA.seq final))))
  apply all.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [ticks, nodes, NamedBody484_185, NamedBody484_184, NamedBody484_154, NamedBody484_152, NamedBody484_153, NamedBody484_151] <;> omega

/-- Actual capacity-clearing suffix through storing the new capacity; no validity assumption is imposed on later loads. -/
theorem capacitySuffixBound {C F : Type} (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_237 (MemzeroCall.pre base length) (fun _ => True)
      (17 * maximumBytes + 517) (maximumBytes + 45) := by
  have tail : BlockBound (C := C) (F := F) NamedBody484_236 (fun _ => True) (fun _ => True) 18 1 :=
    BlockBound.basic _ _ _ (by decide) (fun _ _ _ _ => trivial)
  have all := (capacityBlockBound (C := C) (F := F) base length maximumBytes lengthBound maximumBound).seq tail
  apply all.weaken (fun _ h => h) (fun _ h => h) <;> omega

theorem bounded_capacity_suffix {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length : BitVec 64) (maximumBytes : Nat)
    (lengthBound : length.toNat ≤ maximumBytes) (maximumBound : maximumBytes + 32 < 2 ^ 64)
    (valid : MemzeroCall.pre base length source)
    (execution : evaluate (NamedBody484_237, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (NamedBody484_237, {source with clock := maximumBytes + 46}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work NamedBody484_237 {source with clock := maximumBytes + 46} (17 * maximumBytes + 517) :=
  (capacitySuffixBound base length maximumBytes lengthBound maximumBound).boundedExecution
    (fun _ _ h => h) source post result valid execution notTimeout

end InitECandidate.Solver.GuestWork.ExtendMemoryCalls
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.capacityCallBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.lengthCallBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.lengthBlockBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.suffixBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.bounded_suffix

#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.capacityBlockBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.capacitySuffixBound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryCalls.bounded_capacity_suffix

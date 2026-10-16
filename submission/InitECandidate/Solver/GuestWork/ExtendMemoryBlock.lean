import InitECandidate.Solver.GuestWork.ExtendMemorySetup

namespace InitECandidate.Solver.GuestWork.ExtendMemoryBlock
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted
open ExtendMemoryTransfer (beforeCall afterCall)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Arguments and saved logical extension immediately before the actual call
block reserves its compiler handler frame. -/
def beforeBlock {C F : Type} (base clearLength stack metadata : BitVec 64) (savedMaximum : Nat)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  MemzeroCall.pre base clearLength state ∧
  state.regs.lookup 24 = some (.word stack) ∧
  state.regs.lookup 25 = some (.word metadata) ∧
  ∃ value, state.memory (stack + 32#64) = .word value ∧ value.toNat ≤ savedMaximum

private theorem marker_memory {C F : Type} (source post : StackSemStateFiniteExact 64 C F)
    (stack : BitVec 64) (hstack : source.regs.lookup 24 = some (.word stack))
    (run : evaluate (NamedBody484_154, source) = (none, post)) :
    post.memory (stack + 32#64) = source.memory (stack + 32#64) := by
  rw [NamedBody484_154, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  by_cases domain : source.mdomain stack = true
  all_goals
    simp [NamedBody484_152, NamedBody484_153, evaluate_inst, StackSemInst.instHOL,
      instInteger, assign, wordExp, wordOpHOL, wordOp, memStore, getVar, setVar,
      hstack, domain, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run
  all_goals
    subst post
    simp

private theorem marker_bound {C F : Type} (base clearLength stack metadata : BitVec 64)
    (savedMaximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_154
      (beforeBlock base clearLength stack metadata savedMaximum)
      (beforeBlock base clearLength stack metadata savedMaximum) 3 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  obtain ⟨callee, hstack, hmetadata, value, found, small⟩ := valid
  have a := normalFrame NamedBody484_154 10 (by decide) source post run
  have b := normalFrame NamedBody484_154 11 (by decide) source post run
  have c := normalFrame NamedBody484_154 24 (by decide) source post run
  have d := normalFrame NamedBody484_154 25 (by decide) source post run
  have memory := marker_memory source post stack hstack run
  refine ⟨⟨?_, a.1.trans callee.2.1, b.1.trans callee.2.2⟩,
    c.1.trans hstack, d.1.trans hmetadata, value, ?_, small⟩
  · rw [a.2]
    exact callee.1
  · rw [memory]
    exact found

private theorem frame_bound {C F : Type} (base clearLength stack metadata : BitVec 64)
    (savedMaximum : Nat)
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_183
      (beforeBlock base clearLength stack metadata savedMaximum)
      (beforeCall base clearLength (stack - 24#64) metadata savedMaximum) 29 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  obtain ⟨callee, hstack, hmetadata, saved⟩ := valid
  obtain ⟨code, _, _, stackReg, metadataReg, baseReg, lengthReg, _, savedCell⟩ :=
    ExtendMemorySetup.frame_setup source post stack metadata hstack hmetadata separated run
  refine ⟨⟨?_, baseReg.trans callee.2.1, lengthReg.trans callee.2.2⟩,
    stackReg, metadataReg, ?_⟩
  · rw [code]
    exact callee.1
  · simpa only [BitVec.sub_add_cancel, savedCell] using saved

private theorem skip_bound {C F : Type} (pre : StackSemStateFiniteExact 64 C F → Prop) :
    BlockBound .skip pre pre 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  simp only [evaluate_skip, Prod.mk.injEq, true_and] at run
  subst post
  exact valid

/-- Actual full capacity-clearing call block, now including argument/saved-slot
transfer through its marker and handler setup, call, and return continuation. -/
theorem capacity_block_bound {C F : Type}
    (base clearLength stack metadata : BitVec 64) (clearMaximum savedMaximum : Nat)
    (clearBound : clearLength.toNat ≤ clearMaximum) (maximumBound : clearMaximum + 32 < 2 ^ 64)
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_219
      (beforeBlock base clearLength stack metadata savedMaximum)
      (afterCall (stack - 24#64) metadata savedMaximum)
      (17 * clearMaximum + 499) (clearMaximum + 44) := by
  have call := ExtendMemoryTransfer.capacity_call_bound (C := C) (F := F)
    base clearLength (stack - 24#64) metadata clearMaximum savedMaximum clearBound maximumBound
    (by simpa only [BitVec.sub_add_cancel] using separated)
  have frame := frame_bound (C := C) (F := F) base clearLength stack metadata savedMaximum separated
  have marker := marker_bound (C := C) (F := F) base clearLength stack metadata savedMaximum
  have skipBefore := skip_bound (C := C) (F := F) (beforeBlock base clearLength stack metadata savedMaximum)
  have skipAfter := skip_bound (C := C) (F := F) (beforeCall base clearLength (stack - 24#64) metadata savedMaximum)
  have composed := skipBefore.seq (marker.seq (frame.seq (skipAfter.seq (skipAfter.seq call))))
  have cost := ExtendMemoryCalls.capacityBlockBound (C := C) (F := F)
    base clearLength clearMaximum clearBound maximumBound
  constructor
  · intro source valid
    exact cost.work source valid.1
  · intro source valid
    exact cost.clock source valid.1
  · intro source post valid run
    exact composed.normal source post valid run
  · intro source post valid run
    exact cost.timeout source post valid.1 run

/-- Actual capacity-clearing suffix through EV_MEM_CAP storage with a bounded
logical extension still available for the second memzero call. -/
theorem capacity_suffix_bound {C F : Type}
    (base clearLength stack metadata : BitVec 64) (clearMaximum savedMaximum : Nat)
    (clearBound : clearLength.toNat ≤ clearMaximum) (maximumBound : clearMaximum + 32 < 2 ^ 64)
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64) :
    BlockBound (C := C) (F := F) NamedBody484_237
      (beforeBlock base clearLength stack metadata savedMaximum)
      (afterCall (stack - 24#64) metadata savedMaximum)
      (17 * clearMaximum + 517) (clearMaximum + 45) := by
  have all := (capacity_block_bound (C := C) (F := F) base clearLength stack metadata
    clearMaximum savedMaximum clearBound maximumBound separated).seq
    (ExtendMemoryTransfer.capacity_tail_bound (stack - 24#64) metadata savedMaximum)
  apply all.weaken (fun _ h => h) (fun _ h => h) <;> omega

end InitECandidate.Solver.GuestWork.ExtendMemoryBlock
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryBlock.capacity_block_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryBlock.capacity_suffix_bound

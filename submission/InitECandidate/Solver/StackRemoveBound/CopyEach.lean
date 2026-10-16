import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyEach

/-! Exact extra-clock count for the bitmap pattern copier. All state, memory
frame and native execution conclusions from the original induction are retained. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.StackSemStoreConsts
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CopyEachProof

/-- A successful pattern copy starting within the bitmap cannot run past its end. -/
theorem copyPatternFinalLe {width : Nat} [NeZero width]
    (pattern : BitVec width) (index : Nat) (address offset : BitVec width)
    (bitmaps : List (BitVec width)) (domain : BitVec width → Prop)
    [DecidablePred domain] (memory : BitVec width → WordLocW width)
    (finalIndex : Nat) (finalState : BitVec width × (BitVec width → WordLocW width))
    (initial : index ≤ bitmaps.length)
    (run : copyWordsForPattern pattern index address offset bitmaps domain memory =
      some (finalIndex, finalState)) : finalIndex ≤ bitmaps.length := by
  fun_induction copyWordsForPattern pattern index address offset bitmaps domain memory
  case case1 => cases run
  case case2 => cases run; exact initial
  case case3 pattern index address memory hzero hone guard value nextMemory ih =>
    exact ih (by omega) run
  case case4 => cases run

theorem copyEachBound {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index finalIndex : Nat)
    (pattern address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      copyWordsForPattern pattern index address offset bitmaps domain memory =
        some (finalIndex, finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      StackSemStateOps.getVar 1 target = some (.word pattern) ∧
      (∀ key, domain key → targetDomain key) ∧
      StackSemStateOps.getVar 2 target = some (.word address) ∧
      StackSemStateOps.getVar 3 target = some (.word offset) ∧
      StackSemStateOps.getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (_value : BitVec width) (nextMemory : BitVec width → WordLocW width),
      allowance + index = finalIndex ∧
      StackSemEvaluate.evaluate
        (copyEach temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if pattern = 1 then target.regs else target.regs.updateEq (temporary, .word _value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width finalIndex))}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) := by
  fun_induction copyWordsForPattern pattern index address offset bitmaps domain memory
    generalizing finalIndex finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 index address memory hzero =>
    rcases hypothesis with ⟨success, _distinct, _domain, _good,
      oneRead, _subset, addressRead, _offsetRead, bitmapRead, heap⟩
    cases success
    refine ⟨0, 0, target.memory, by omega, ?_, heap⟩
    simp only [Nat.add_zero, ite_true]
    rw [sentinelPostState bitmap index base address target oneRead addressRead bitmapRead]
    exact copyEachSentinel temporary bitmap target oneRead
  case case4 => cases hypothesis.1
  case case3 pattern index address memory hzero hone guard value nextMemory ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good,
      patternRead, subset, addressRead, offsetRead, bitmapRead, heap⟩
    have canonicalHeap := heap
    rw [domainEq] at canonicalHeap
    have canonicalSubset := subset
    rw [domainEq] at canonicalSubset
    let post := copyStepState temporary bitmap index pattern address offset base value target
    have step := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest target distinct good patternRead addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    obtain ⟨nextPatternRead, nextAddressRead, nextOffsetRead, nextBitmapRead, nextClock⟩ :=
      copyStepReads temporary bitmap index pattern address offset base value target distinct offsetRead
    have memoryEq : nextMemory =
        (fun key => if key = address then
          .word (if pattern.getLsbD 0 then value + offset else value) else memory key) := by
      funext key
      by_cases same : key = address <;>
        by_cases bit : pattern.getLsbD 0 = true <;> simp [nextMemory, same, bit]
    have nextHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL nextMemory domain) (SetSep.fun2Set (post.memory, targetDomain)) := by
      simpa only [memoryEq, post, value, copyStepState, domainEq] using step.2
    obtain ⟨allowance, finalValue, resultMemory, used, recursiveRun, finalHeap⟩ :=
      ih finalIndex finalAddress finalMemory post
        ⟨success, distinct, domainEq, good, nextPatternRead, subset,
          by simpa only [bytesInWord] using nextAddressRead,
          nextOffsetRead, nextBitmapRead, nextHeap⟩
    let boosted : StackSemStateFiniteExact width C F :=
      {target with clock := target.clock + (allowance + 1)}
    let boostedPost : StackSemStateFiniteExact width C F :=
      {post with clock := target.clock + (allowance + 1)}
    have boostedStep := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest boosted distinct good patternRead addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    have boostedRun : StackSemEvaluate.evaluate
        (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
          Compiler.Backend.StackLang.addBytesInWordInst bitmap,
          .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
          rightShiftInst 1 1, storeInst temporary 2,
          Compiler.Backend.StackLang.addBytesInWordInst 2], boosted) = (none, boostedPost) := by
      simpa only [boosted, boostedPost, post, copyStepState, value] using boostedStep.1
    have reentry := copyEachReenter temporary bitmap pattern boosted boostedPost
      patternRead hone (by dsimp [boosted]; omega) rfl boostedRun
    have reentryState : StackSemStateOps.decClock boostedPost =
        {post with clock := post.clock + allowance} := by
      simp [StackSemStateOps.decClock, boostedPost, post, copyStepState]
    refine ⟨allowance + 1,
      (if pattern >>> (1 : Nat) = 1 then
        (if pattern.getLsbD 0 then value + offset else value) else finalValue),
      resultMemory, by omega, ?_, finalHeap⟩
    change StackSemEvaluate.evaluate (copyEach temporary bitmap, boosted) = _
    rw [reentry, reentryState, recursiveRun]
    simp only [hone, if_false, post, copyStepState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tTwo : temporary ≠ 2 := by omega
    have tb : temporary ≠ bitmap := by omega
    by_cases nextSentinel : pattern >>> (1 : Nat) = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [nextSentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]


#print axioms InitECandidate.Solver.StackRemoveBound.copyPatternFinalLe
#print axioms InitECandidate.Solver.StackRemoveBound.copyEachBound
end InitECandidate.Solver.StackRemoveBound

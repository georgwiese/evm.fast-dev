import InitECandidate.Solver.StackRemoveBound.CopyEach
import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyLoop

/-! Successful constant copying consumes at most one extra Stack clock per
remaining bitmap word, retaining the original execution and heap assertions. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack StackSemEvaluate StackSemStateOps Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CopyLoopProof

theorem copyLoopBound {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index _unusedIndex : Nat)
    (address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory =
        some (finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      (∀ key, domain key → targetDomain key) ∧
      getVar 2 target = some (.word address) ∧
      getVar 3 target = some (.word offset) ∧
      getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (unchanged : Bool) (value nextBitmap : BitVec width)
      (nextMemory : BitVec width → WordLocW width),
      allowance ≤ bitmaps.length - index ∧
      evaluate (copyLoop temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if unchanged then target.regs else target.regs.updateEq (temporary, .word value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word nextBitmap)}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) := by
  fun_induction StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory
    generalizing finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 => cases hypothesis.1
  case case3 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    obtain ⟨allowance, value, resultMemory, used, copyRun, copiedHeap⟩ :=
      copyEachBound temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, heap⟩
    let copied : StackSemStateFiniteExact width C F :=
      {loaded with memory := resultMemory, regs := (((if pattern = 1 then loaded.regs else loaded.regs.updateEq (temporary, .word value)).updateEq (2, .word nextAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width nextIndex))}
    change evaluate (copyEach temporary bitmap,
      {loaded with clock := loaded.clock + allowance}) = (none, copied) at copyRun
    have bTwo : bitmap ≠ 2 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have bThree : bitmap ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have tThree : temporary ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have copiedReads : getVar 2 copied = some (.word nextAddress) ∧
        getVar 3 copied = some (.word offset) ∧
        getVar bitmap copied = some (.word
          (base + bytesInWord width * BitVec.ofNat width nextIndex)) := by
      change target.regs.lookup 3 = _ at offsetRead
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
        simp [copied, loaded, loadBitmapState, getVar, sentinel,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          Ne.symm bTwo, Ne.symm bThree, Ne.symm tThree, offsetRead]
    obtain ⟨recursiveAllowance, unchanged, recursiveValue, nextBitmap,
      finalTargetMemory, recursiveBound, recursiveRun, finalHeap⟩ :=
      ih finalAddress finalMemory copied
        ⟨success, distinct, domainEq, good, subset,
          copiedReads.1, copiedReads.2.1, copiedReads.2.2, copiedHeap⟩
    have nextValid : nextIndex < bitmaps.length := by
      by_contra outside
      have outside : bitmaps.length ≤ nextIndex := by omega
      rw [StackSemStoreConsts.copyWordsExact, dif_pos outside] at success
      cases success
    let boosted := {target with clock := target.clock + (allowance + recursiveAllowance + 1)}
    let boostedLoaded := {loaded with clock := loaded.clock + (allowance + recursiveAllowance + 1)}
    let boostedCopied := {copied with clock := copied.clock + (recursiveAllowance + 1)}
    let next := loadBitmapState bitmap nextIndex base bitmaps[nextIndex] boostedCopied
    have firstRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      boosted distinct valid bitmapRead (by simpa [domainEq] using heap)
    have firstState : loadBitmapState bitmap i base bitmaps[i] boosted = boostedLoaded := by
      simp only [← patternEq, boosted, boostedLoaded, loaded, loadBitmapState]
    rw [firstState] at firstRun
    have boostedCopyRun := Compiler.Backend.StackProps.evaluateAddClock
      (recursiveAllowance + 1) (copyEach temporary bitmap)
      {loaded with clock := loaded.clock + allowance} none copied ⟨copyRun, by simp⟩
    have boostedCopy : evaluate (copyEach temporary bitmap, boostedLoaded) =
        (none, boostedCopied) := by
      simpa only [boostedLoaded, boostedCopied, Nat.add_assoc] using boostedCopyRun
    have reloadRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], boostedCopied) =
        (none, next) :=
      loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        boostedCopied distinct nextValid copiedReads.2.2
        (by simpa [domainEq, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
    have reloadDecRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], decClock boostedCopied) =
        (none, decClock next) := by
      have run := loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        (decClock boostedCopied) distinct nextValid copiedReads.2.2
        (by simpa [domainEq, decClock, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
      simpa only [next, loadBitmapState, decClock] using run
    have nonzero : next.clock ≠ 0 := by
      dsimp [next, loadBitmapState, boostedCopied]
      omega
    have loopRun := copyLoopNegative temporary bitmap pattern boosted boostedLoaded
      boostedCopied next firstRun reads.1 sign boostedCopy reloadRun reloadDecRun nonzero
    have reentryState : decClock boostedCopied =
        {copied with clock := copied.clock + recursiveAllowance} := by
      simp [decClock, boostedCopied]
    refine ⟨allowance + recursiveAllowance + 1,
      decide (pattern = 1) && unchanged, (if unchanged then value else recursiveValue),
      nextBitmap, finalTargetMemory, by omega, ?_, finalHeap⟩
    change evaluate (copyLoop temporary bitmap, boosted) = _
    rw [loopRun, reentryState, recursiveRun]
    dsimp only [copied, loaded, loadBitmapState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tTwo : temporary ≠ 2 := by omega
    have tb : temporary ≠ bitmap := by omega
    cases unchanged <;>
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  case case4 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    cases Option.some.inj success
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by
      simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    have loadedHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL m domain) (SetSep.fun2Set (loaded.memory, targetDomain)) := heap
    obtain ⟨allowance, value, resultMemory, used, copyRun, finalHeap⟩ :=
      copyEachBound temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, loadedHeap⟩
    have finalLe := copyPatternFinalLe pattern (i + 1) a offset bitmaps domain m
      nextIndex (nextAddress, nextMemory) (by omega) patternRun
    have prefixRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      {target with clock := target.clock + allowance} distinct valid bitmapRead
      (by simpa [domainEq] using heap)
    have prefixLoaded : loadBitmapState bitmap i base bitmaps[i]
        {target with clock := target.clock + allowance} =
        {loaded with clock := loaded.clock + allowance} := by
      simp only [← patternEq, loaded, loadBitmapState]
    rw [prefixLoaded] at prefixRun
    have nonnegative : pattern.msb = false := by simpa using sign
    have loopRun := copyLoopNonnegative temporary bitmap pattern
      {target with clock := target.clock + allowance}
      {loaded with clock := loaded.clock + allowance} prefixRun reads.1 nonnegative
    refine ⟨allowance, decide (pattern = 1), value,
      base + bytesInWord width * BitVec.ofNat width nextIndex,
      resultMemory, by omega, ?_, finalHeap⟩
    rw [loopRun, copyRun]
    dsimp only [loaded, loadBitmapState]
    congr 2
    apply HolFiniteMapExact.ext_lookup
    intro query
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    have tOne : temporary ≠ 1 := by omega
    have tb : temporary ≠ bitmap := by omega
    by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
      by_cases qBitmap : query = bitmap <;>
      by_cases qOne : query = 1 <;>
      by_cases qTwo : query = 2 <;>
      by_cases qTemporary : query = temporary <;>
      simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tb,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]


#print axioms InitECandidate.Solver.StackRemoveBound.copyLoopBound
end InitECandidate.Solver.StackRemoveBound

import InitECandidate.Solver.JumpDest.StepMapped

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def loopState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (memory : WitnessRadix.WordWrites.Memory) (spent : Nat) (index : BitVec 64) :=
  WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - spent} "pc" index

/-- The complete original bytecode scan, without a cryptographic or opcode
content premise. Strict actual PC progress bounds the number of iterations
by the remaining byte length. The result is a full state description, with
all earlier words above the bitmap preserved and exact used source clocks.
Mapped regions, typed entry locals and enough clocks are explicit. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap code index length : BitVec 64)
    (bmLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (fits : length.toNat + 32 < 2 ^ 64)
    (codeMapped : ∀ offset < length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress code offset)))
    (bitmapMapped : ∀ offset, offset + 8 ≤ bitmapBytes length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress bitmap offset))
    (enough : length.toNat - index.toNat ≤ source.clock) :
    ∃ (memory : WitnessRadix.WordWrites.Memory) (finish : BitVec 64) (spent : Nat),
      evaluateHOLFiniteState source loop = (none, loopState source memory spent finish) ∧
      length.toNat ≤ finish.toNat ∧ spent ≤ length.toNat - index.toNat ∧
      ∀ query : BitVec 64, bitmap.toNat + bitmapBytes length.toNat ≤ query.toNat → memory query = source.memory query := by
  classical
  generalize rankEq : length.toNat - index.toNat = rank
  induction rank using Nat.strong_induction_on generalizing source index with
  | h rank ih =>
    have test : eval source condition = some (.val (.word (flag (index < length)))) := by
      simp [eval, condition, localVar, evalHOLExact, toExact, pcLocal, nLocal, flag,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at test
    by_cases active : index < length
    · have inside : index.toNat < length.toNat := active
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      obtain ⟨opcode, nextByte, old, bodyRun, progress, upper⟩ :=
        step_of_mapped entry bitmap code index length bmLocal codeLocal pcLocal nLocal inside fits codeMapped bitmapMapped
      let newIndex := index + selectedAdvance opcode index length nextByte
      let next := stepState entry bitmap opcode index length nextByte old
      have newRank : length.toNat - newIndex.toNat < rank := by
        rw [← rankEq]
        exact Nat.sub_lt_sub_left inside progress
      have nextBm : next.locals.lookup (ofString "bm") = some (.val (.word bitmap)) :=
        (bind_lookup_other _ "pc" "bm" _ (by decide)).trans bmLocal
      have nextCode : next.locals.lookup (ofString "code") = some (.val (.word code)) :=
        (bind_lookup_other _ "pc" "code" _ (by decide)).trans codeLocal
      have nextLength : next.locals.lookup (ofString "n") = some (.val (.word length)) :=
        (bind_lookup_other _ "pc" "n" _ (by decide)).trans nLocal
      have nextPc : next.locals.lookup (ofString "pc") = some (.val (.word newIndex)) := bind_lookup_same _ _ _
      have nextEnough : length.toNat - newIndex.toNat ≤ next.clock := by
        change length.toNat - newIndex.toNat ≤ source.clock - 1
        omega
      obtain ⟨memory, finish, spent, tailRun, stopped, spentBound, protectedWords⟩ :=
        ih (length.toNat - newIndex.toNat) newRank next newIndex nextBm nextCode nextPc nextLength
          codeMapped bitmapMapped nextEnough rfl
      have finalShape : loopState next memory spent finish = loopState source memory (spent + 1) finish := by
        change WitnessRadix.QueryBranch.bind
          (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - 1 - spent}
            "pc" newIndex) "pc" finish = _
        rw [bind_overwrite]
        have clocks : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
        simp only [loopState, clocks]
      have loopRun : evaluateHOLFiniteState source loop = (none, loopState source memory (spent + 1) finish) := by
        rw [loop, evaluateHOLFiniteState_while_total]
        simp only [evalHOLFinite]
        rw [test]
        simp only [flag, if_pos active]
        rw [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide)]
        simp only [if_neg positive]
        change evaluateHOLFiniteState entry step = (none, next) at bodyRun
        rw [bodyRun]
        rw [WitnessRadix.StateSteps.fixed_clock entry next none (Nat.le_refl _)]
        change evaluateHOLFiniteState next loop = _
        rw [tailRun, finalShape]
      refine ⟨memory, finish, spent + 1, loopRun, stopped, ?_, ?_⟩
      · omega
      · intro query below
        have preserved := protectedWords query below
        have oneStep := step_away entry bitmap opcode index length nextByte old query inside below
        exact preserved.trans oneStep
    · refine ⟨source.memory, index, 0, ?_, ?_, by omega, ?_⟩
      · have same : loopState source source.memory 0 index = source := by
          simpa only [loopState, Nat.sub_zero] using bind_existing source "pc" index pcLocal
        rw [loop, evaluateHOLFiniteState_while_total]
        simp only [evalHOLFinite]
        rw [test]
        simp [flag, active, same]
      · change ¬ index.toNat < length.toNat at active
        omega
      · intro query below
        rfl

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.loop_execute

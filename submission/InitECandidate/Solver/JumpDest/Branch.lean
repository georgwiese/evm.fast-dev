import InitECandidate.Solver.JumpDest.Advance
import InitECandidate.Solver.JumpDest.Mark

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem choose {F : Type} (source : PanSemStateFiniteExact 64 F) (test : ExpHOL 64)
    (left right : ProgHOL 64) (condition : Prop) [Decidable condition]
    (read : eval source test = some (.val (.word (flag condition)))) :
    evaluateHOLFiniteState source (.ite test left right) =
      (if condition then evaluateHOLFiniteState source left else evaluateHOLFiniteState source right) := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_ite, read]
  by_cases passed : condition <;> simp [flag, passed]

noncomputable def branchState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory := by
  classical
  exact if opcode = 91#64 then
    {source with memory := WitnessRadix.StoreWord.put source.memory (bitmap + wordOffset index) (setBit old index)}
  else WitnessRadix.QueryBranch.bind source "adv" (selectedAdvance opcode index length next)

/-- The full actual opcode-selection branch. It either marks its one bitmap
word or computes exactly the checked positive advance; every other field and
all protected earlier memory are retained by the explicit resulting state. -/
theorem branch_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old : BitVec 64)
    (bmLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word opcode)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (advLocal : source.locals.lookup (ofString "adv") = some (.val (.word 1#64)))
    (loaded : index + 1#64 < length → eval source nextByte = some (.val (.word next)))
    (mapped : source.memaddrs (bitmap + wordOffset index))
    (cell : source.memory (bitmap + wordOffset index) = .word old) :
    evaluateHOLFiniteState source branch = (none, branchState source bitmap opcode index length next old) := by
  classical
  have marker := equal_read source "op" opcode 91#64 opLocal
  rw [branch, choose source _ _ _ _ marker]
  by_cases isMark : opcode = 91#64
  · rw [if_pos isMark]
    simpa only [branchState, if_pos isMark] using mark_execute source bitmap index old bmLocal pcLocal mapped cell
  · rw [if_neg isMark]
    have push := range_read source "op" opcode 96#64 127#64 opLocal
    rw [choose source pushTest _ _ _ push]
    by_cases range : ¬ opcode < 96#64 ∧ ¬ 127#64 < opcode
    · rw [if_pos range]
      simpa only [branchState, if_neg isMark, selectedAdvance, if_pos range] using push_execute source opcode 1#64 opLocal advLocal
    · rw [if_neg range]
      have wide := wide_read source opcode opLocal
      by_cases isWide : opcode = 230#64 ∨ opcode = 231#64
      · have not232 : opcode ≠ 232#64 := by
          rcases isWide with rfl | rfl <;> decide
        let stage := WitnessRadix.QueryBranch.bind source "adv" (continuationWord index length next 91#64)
        have first : evaluateHOLFiniteState source (.ite wideTest (continuationAdvance "nx" 91#64) .skip) = (none, stage) := by
          rw [choose source wideTest _ _ _ wide, if_pos isWide]
          exact continuation_execute source "nx" 91#64 index length next 1#64 (by decide) advLocal pcLocal nLocal loaded
        have stageOp : stage.locals.lookup (ofString "op") = some (.val (.word opcode)) :=
          (bind_lookup_other source "adv" "op" _ (by decide)).trans opLocal
        have last := equal_read stage "op" opcode 232#64 stageOp
        rw [WitnessRadix.StateSteps.next_sequence source stage _ _ first (Nat.le_refl _),
          choose stage _ _ _ _ last, if_neg not232, evaluateHOLFiniteState_skip]
        simp only [branchState, if_neg isMark, selectedAdvance, if_neg range, if_neg not232, if_pos isWide]
        rfl
      · have first : evaluateHOLFiniteState source (.ite wideTest (continuationAdvance "nx" 91#64) .skip) = (none, source) := by
          rw [choose source wideTest _ _ _ wide, if_neg isWide, evaluateHOLFiniteState_skip]
        rw [WitnessRadix.StateSteps.next_sequence source source _ _ first (Nat.le_refl _)]
        have last := equal_read source "op" opcode 232#64 opLocal
        rw [choose source _ _ _ _ last]
        by_cases is232 : opcode = 232#64
        · rw [if_pos is232]
          have run := continuation_execute source "nx2" 82#64 index length next 1#64 (by decide) advLocal pcLocal nLocal loaded
          simpa only [branchState, if_neg isMark, selectedAdvance, if_neg range, if_pos is232] using run
        · rw [if_neg is232, evaluateHOLFiniteState_skip]
          simp only [branchState, if_neg isMark, selectedAdvance, if_neg range, if_neg is232, if_neg isWide]
          rw [bind_existing source "adv" 1#64 advLocal]

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.branch_execute

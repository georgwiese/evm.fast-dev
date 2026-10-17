import InitECandidate.Solver.JumpDest.Continuation

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem bind_existing {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (word : BitVec 64)
    (stored : source.locals.lookup (ofString name) = some (.val (.word word))) :
    WitnessRadix.QueryBranch.bind source name word = source := by
  unfold WitnessRadix.QueryBranch.bind setVarHOLFinite
  conv_rhs => rw [← show {source with locals := source.locals} = source from rfl]
  congr 1
  apply HolFiniteMapExact.ext
  funext query
  by_cases same : ofString name = query
  · subst query
    simp [HolFiniteMapExact.update, FUPDATE, stored]
  · simp [HolFiniteMapExact.update, FUPDATE, same]

theorem equal_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (word literal : BitVec 64)
    (stored : source.locals.lookup (ofString name) = some (.val (.word word))) :
    eval source (.cmp .equal (localVar name) (.const literal)) = some (.val (.word (flag (word = literal)))) := by
  classical
  by_cases same : word = literal <;>
    simp [eval, evalHOLExact, localVar, toExact, stored, flag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, same]

def pushedWord (opcode : BitVec 64) : BitVec 64 := opcode - 96#64 + 2#64

/-- The actual PUSH assignment, including the source's word arithmetic. -/
theorem push_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (opcode old : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word opcode)))
    (advLocal : source.locals.lookup (ofString "adv") = some (.val (.word old))) :
    evaluateHOLFiniteState source pushAdvance = (none, WitnessRadix.QueryBranch.bind source "adv" (pushedWord opcode)) := by
  have read : eval source (.op .add [.op .sub [localVar "op", .const 96#64], .const 2#64]) =
      some (.val (.word (pushedWord opcode))) := by
    simp [eval, pushedWord, evalHOLExact, evalListHOLExact, localVar, toExact, opLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  exact WitnessRadix.StateSteps.assign_execute source "adv" _ old _ advLocal read

theorem pushed_number (opcode : BitVec 64) (lower : ¬ opcode < 96#64) (upper : ¬ 127#64 < opcode) :
    (pushedWord opcode).toNat = opcode.toNat - 96 + 2 ∧
      2 ≤ (pushedWord opcode).toNat ∧ (pushedWord opcode).toNat ≤ 33 := by
  have low : 96 ≤ opcode.toNat := by change ¬ opcode.toNat < 96 at lower; omega
  have high : opcode.toNat ≤ 127 := by change ¬ 127 < opcode.toNat at upper; omega
  have funded : (96#64 : BitVec 64) ≤ opcode := low
  have difference := BitVec.toNat_sub_of_le funded
  change (opcode - 96#64).toNat = opcode.toNat - 96 at difference
  have number : (pushedWord opcode).toNat = opcode.toNat - 96 + 2 := by
    unfold pushedWord
    rw [BitVec.toNat_add_of_lt (by rw [difference]; change opcode.toNat - 96 + 2 < 2 ^ 64; omega), difference]
    rfl
  exact ⟨number, by omega, by omega⟩

noncomputable def selectedAdvance (opcode index length next : BitVec 64) : BitVec 64 := by
  classical
  exact if opcode = 91#64 then 1#64
    else if ¬ opcode < 96#64 ∧ ¬ 127#64 < opcode then pushedWord opcode
    else if opcode = 232#64 then continuationWord index length next 82#64
    else if opcode = 230#64 ∨ opcode = 231#64 then continuationWord index length next 91#64
    else 1#64

theorem continuation_bound (index length next low : BitVec 64) :
    1 ≤ (continuationWord index length next low).toNat ∧ (continuationWord index length next low).toNat ≤ 2 := by
  classical
  unfold continuationWord
  split <;> decide

/-- The exact selector used for branch execution is always positive and at
most33, independent of bytecode contents or whether a continuation is present. -/
theorem selected_bounds (opcode index length next : BitVec 64) :
    1 ≤ (selectedAdvance opcode index length next).toNat ∧
      (selectedAdvance opcode index length next).toNat ≤ 33 := by
  classical
  unfold selectedAdvance
  split
  · decide
  · split
    · rename_i isMark range
      have pushed := pushed_number opcode range.1 range.2
      omega
    · split
      · have bound := continuation_bound index length next 82#64
        omega
      · split
        · have bound := continuation_bound index length next 91#64
          omega
        · decide

theorem selected_progress (opcode index length next : BitVec 64)
    (inside : index.toNat < length.toNat) (fits : length.toNat + 32 < 2 ^ 64) :
    (index + selectedAdvance opcode index length next).toNat = index.toNat + (selectedAdvance opcode index length next).toNat ∧
      index.toNat < (index + selectedAdvance opcode index length next).toNat ∧
      (index + selectedAdvance opcode index length next).toNat ≤ length.toNat + 32 := by
  have bounds := selected_bounds opcode index length next
  have number := BitVec.toNat_add_of_lt (show index.toNat + (selectedAdvance opcode index length next).toNat < 2 ^ 64 from by omega)
  exact ⟨number, by omega, by omega⟩

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.bind_existing
#print axioms InitECandidate.Solver.JumpDest.push_execute
#print axioms InitECandidate.Solver.JumpDest.pushed_number
#print axioms InitECandidate.Solver.JumpDest.selected_bounds
#print axioms InitECandidate.Solver.JumpDest.selected_progress

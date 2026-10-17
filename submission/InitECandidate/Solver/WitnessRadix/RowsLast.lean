import InitECandidate.Solver.WitnessRadix.RowsFrame
import InitECandidate.Solver.WitnessRadix.TerminalReads

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rows_last (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) (index : Nat) (input : List (BitVec 64)) (ordinal : BitVec 64)
    (rows : Rows memory domain base start index input) (last : input.getLast? = some ordinal) :
    domain (row base start (BitVec.ofNat 64 (index + input.length - 1))) ∧
      memory (row base start (BitVec.ofNat 64 (index + input.length - 1))) = .word ordinal := by
  induction input generalizing index with
  | nil => simp at last
  | cons value rest ih =>
      cases rest with
      | nil =>
          have same : value = ordinal := by simpa using last
          subst value
          simpa only [List.length_cons, List.length_nil, Nat.add_zero, Nat.add_sub_cancel] using ⟨rows.1, rows.2.1⟩
      | cons next tail =>
          have last' : (next :: tail).getLast? = some ordinal := by simpa using last
          have tailRows := ih (index + 1) rows.2.2 last'
          have address : index + (value :: next :: tail).length - 1 = index + 1 + (next :: tail).length - 1 := by
            simp only [List.length_cons]
            omega
          simpa only [address] using tailRows

theorem terminal_address (base : BitVec 64) (start count : Nat) (present : 0 < count) :
    base + ((BitVec.ofNat 64 start + BitVec.ofNat 64 count) - 1#64) * 8#64 =
      row base (BitVec.ofNat 64 start) (BitVec.ofNat 64 (0 + count - 1)) := by
  have countEq : count = (count - 1) + 1 := by omega
  rw [countEq, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have back : count - 1 + 1 - 1 = count - 1 := by omega
  simp only [row, Nat.zero_add, back]

/-- A logical final ordinal stored in a readable interval supplies the actual
terminal load expression, with no extra memory-read assumption. -/
theorem terminal_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src : BitVec 64) (start : Nat) (input : List (BitVec 64)) (ordinal : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word (BitVec.ofNat 64 start))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length))))
    (rows : Rows source.memory source.memaddrs src (BitVec.ofNat 64 start) 0 input)
    (last : input.getLast? = some ordinal) :
    QueryBranch.eval source TerminalProgram.ordinalExpression = some (.val (.word ordinal)) := by
  have present : input ≠ [] := by intro empty; subst input; simp at last
  have lastRow := rows_last _ _ _ _ 0 input ordinal rows last
  apply TerminalProgram.ordinal_read source src _ _ ordinal srcLocal startLocal countLocal
  · rw [terminal_address src start input.length (List.length_pos_iff.mpr present)]
    exact lastRow.1
  · rw [terminal_address src start input.length (List.length_pos_iff.mpr present)]
    exact lastRow.2

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.rows_last
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.terminal_read

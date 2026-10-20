import InitECandidate.Solver.Input.HeaderEntry

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Passing the actual three leading guards spends no source clock and
exposes the literal shifted first-container tail at every clock budget. -/
theorem passing_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))))
    (extent : 18 ≤ input.length % 2^64) (tag : Guest.GasLimit.byte input 0 = 21) (version : Guest.GasLimit.byte input 1 = 1) :
    evaluateHOLFiniteState source body = evaluateHOLFiniteState (shifted source pointer (input.length % 2^64)) afterHeader := by
  have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  have firstRead := length_read source (input.length % 2^64) 2 small (by decide) lengthLocal
  let entered := shifted source pointer (input.length % 2^64)
  have shiftedLength : entered.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) := bind_lookup_same _ _ _
  have thirdRead := length_read entered (input.length % 2^64 - 2) 16 (by omega) (by decide) shiftedLength
  have secondRead := schema_read source input pointer heap (by omega) pointerLocal
  simp only [eval,if_neg (show ¬ input.length % 2^64 < 2 by omega)] at firstRead
  simp only [eval,if_neg (show ¬ input.length % 2^64 - 2 < 16 by omega)] at thirdRead
  simp only [eval,tag,version,ne_eq,not_true_eq_false,or_self,if_false] at secondRead
  have first : evaluateHOLFiniteState source (lengthGuard 2 1) = (none,source) := by
    rw [lengthGuard,evaluateHOLFiniteState_ite,firstRead]
    simp
  have second : evaluateHOLFiniteState source schemaGuard = (none,source) := by
    rw [schemaGuard,evaluateHOLFiniteState_ite,secondRead]
    simp
  have third : evaluateHOLFiniteState entered (lengthGuard 16 80) = (none,entered) := by
    rw [lengthGuard,evaluateHOLFiniteState_ite,thirdRead]
    simp
  have shift := shift_execute source pointer (input.length % 2^64) small (by omega) pointerLocal lengthLocal
  rw [entry_shape,StateSteps.next_sequence source source _ _ first (Nat.le_refl _),
    StateSteps.next_sequence source source _ _ second (Nat.le_refl _)]
  rw [StateSteps.next_sequence source (QueryBranch.bind source "p" (pointer + 2#64)) _ _ shift.2.1 (Nat.le_refl _),
    StateSteps.next_sequence (QueryBranch.bind source "p" (pointer + 2#64)) (shifted source pointer (input.length % 2^64)) _ _ shift.2.2 (Nat.le_refl _),StateSteps.next_sequence entered entered _ _ third (Nat.le_refl _)]

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.passing_entry
